"""Fast reporting regressions; no Agda, Nix builds, generator, or Pilot runs."""
import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
import ast
import sys
import runpy
from unittest.mock import patch

from test_runner import Cases, SUMMARY_MARKER

from ci_diagnostics import MARKER, assertion_failure, command_failure, summarize

REPOSITORY = Path(__file__).resolve().parent.parent


class DiagnosticsTests(unittest.TestCase):
    def test_actual_integration_helpers_emit_failure_details(self):
        tree = ast.parse((REPOSITORY / 'test/integration.py').read_text())
        helpers = [node for node in ast.walk(tree) if isinstance(node, ast.FunctionDef)
                   and node.name in ('run_automatic', 'run')]
        self.assertEqual(len(helpers), 2)
        with tempfile.TemporaryDirectory(prefix='ci-report-test-') as temporary:
            output = Path(temporary)
            (output / 'diagnostics.json').write_text(json.dumps({'diagnostics': [{'symbol': 'Actual.Failure', 'message': 'missing body'}]}))
            namespace = {'generator': 'generator', 'work': output, 'os': os, 'sys': sys,
                         'subprocess': subprocess, 'command_failure': command_failure}
            exec(compile(ast.Module(body=helpers, type_ignores=[]), 'integration-helpers', 'exec'), namespace)
            result = subprocess.CompletedProcess([], 2, '', 'compiler stderr')
            for name, arguments in [('run_automatic', ('Root', output, 0)), ('run', ('generate', 'mapping.yaml', output, 0))]:
                captured = io.StringIO()
                with patch.object(subprocess, 'run', return_value=result), contextlib.redirect_stdout(captured):
                    with self.assertRaisesRegex(AssertionError, 'Expected exit 0; actual exit 2'):
                        namespace[name](*arguments)
                receipt = json.loads(captured.getvalue().split(MARKER)[1])
                self.assertEqual(receipt['diagnostics.json']['diagnostics'][0]['symbol'], 'Actual.Failure')

    def test_command_receipt_survives_bundle_cleanup(self):
        with tempfile.TemporaryDirectory(prefix='ci-report-test-') as temporary:
            bundle = Path(temporary)
            (bundle / 'manifest.json').write_text(json.dumps({'complete': False, 'targetValidation': 'accepted'}))
            (bundle / 'diagnostics.json').write_text(json.dumps({'diagnostics': [{
                'symbol': 'Example.Box.contents', 'code': 'unsupported-syntax',
                'message': 'No checked first-order body', 'causes': [{'rule': 'native.algebraic-cases'}]}]}))
            output = io.StringIO()
            result = subprocess.CompletedProcess(['generator'], 2, 'model output', 'compiler error')
            with contextlib.redirect_stdout(output):
                message = command_failure(['generator', 'generate', 'path with spaces'], 0, result, bundle)
            receipt = json.loads(output.getvalue().split(MARKER, 1)[1])
        self.assertEqual(receipt['expectedExit'], 0)
        self.assertEqual(receipt['actualExit'], 2)
        self.assertEqual(receipt['diagnostics.json']['diagnostics'][0]['symbol'], 'Example.Box.contents')
        self.assertIn('No checked first-order body', message)
        self.assertIn("'path with spaces'", message)
        self.assertEqual(receipt['stderr'], 'compiler error')

    def test_missing_or_malformed_diagnostics_do_not_hide_original_status(self):
        with tempfile.TemporaryDirectory(prefix='ci-report-test-') as temporary:
            bundle = Path(temporary)
            for text in (None, 'not JSON'):
                if text is not None:
                    (bundle / 'diagnostics.json').write_text(text)
                output = io.StringIO()
                with contextlib.redirect_stdout(output):
                    message = command_failure(['generator'], 0, subprocess.CompletedProcess([], 1, '', 'Agda failed'), bundle)
                self.assertIn('actual exit 1', message)
                self.assertIn('Agda failed', message)
                self.assertIn('unavailable', json.loads(output.getvalue().split(MARKER)[1])['diagnostics.json'])

    def test_assertion_shows_actual_counts_and_evidence(self):
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            assertion_failure('expected 18 instances', {'instances': list(range(37)),
                              'multi_callback_evidence': {'bodyMutationsDetected': 8}, 'inventory': {'large': True}})
        receipt = json.loads(output.getvalue().split(MARKER)[1])
        self.assertEqual(receipt['counts'], {'instances': 37})
        self.assertEqual(receipt['evidence']['multi_callback_evidence']['bodyMutationsDetected'], 8)
        self.assertNotIn('inventory', receipt['evidence'])

    def test_shell_wrapper_preserves_command_exit_and_complete_log(self):
        with tempfile.TemporaryDirectory(prefix='ci-report-test-') as temporary:
            directory = Path(temporary)
            command = ['bash', '-c', 'for ((i=0;i<100;i++)); do echo "line $i"; done; echo last-error >&2; exit 7']
            result = subprocess.run(['bash', str(REPOSITORY / '.github/run-check.sh'), 'integration', *command],
                env={**os.environ, 'CI_DIAGNOSTICS_DIR': temporary}, capture_output=True, text=True)
            self.assertEqual(result.returncode, 7)
            self.assertEqual((directory / 'integration.exit').read_text().strip(), '7')
            log = (directory / 'integration.log').read_text()
            self.assertIn('line 0\n', log)
            self.assertIn('line 99\n', log)
            self.assertIn('last-error', log)
            self.assertIn('::error title=integration check failed::Exit 7', result.stdout)

    def test_summary_extracts_nix_prefixed_receipt_and_escapes_markup(self):
        with tempfile.TemporaryDirectory(prefix='ci-report-test-') as temporary:
            directory = Path(temporary)
            (directory / 'integration.exit').write_text('1\n')
            (directory / 'integration.command').write_text('nix build .#checks.x86_64-linux.integration\n')
            receipt = {'expectedExit': 0, 'actualExit': 2, 'diagnostics.json': {'diagnostics': [
                {'symbol': 'Example.Lift.lower', 'message': 'Missing <body>'}]}, 'stdout': 'full output', 'stderr': 'stderr'}
            (directory / 'integration.log').write_text('agda2sysml-integration> ' + MARKER + json.dumps(receipt) + '\n<script>alert(1)</script>\n')
            summary = directory / 'job-summary.md'
            summarize(directory, summary)
            text = summary.read_text()
            self.assertIn('Failed (exit 1)', text)
            self.assertIn('"expectedExit": 0', text.replace('&quot;', '"'))
            self.assertIn('Example.Lift.lower', text)
            self.assertIn('Missing &lt;body&gt;', text)
            self.assertNotIn('<script>', text)
            self.assertEqual(json.loads((directory / 'integration-failure-1.json').read_text()), receipt)
            self.assertEqual((directory / 'summary.md').read_text(), text)

    def test_skipped_integration_reports_failed_build_prerequisite(self):
        with tempfile.TemporaryDirectory(prefix='ci-report-test-') as temporary:
            directory = Path(temporary)
            (directory / 'generator.exit').write_text('1\n')
            (directory / 'generator.command').write_text('build generator\n')
            (directory / 'generator.log').write_text('compiler failure\n')
            destination = directory / 'job-summary.md'
            summarize(directory, destination)
            self.assertIn('integration | Blocked by failed generator', destination.read_text())

    def test_success_is_not_reported_as_failure(self):
        with tempfile.TemporaryDirectory(prefix='ci-report-test-') as temporary:
            result = subprocess.run(['bash', str(REPOSITORY / '.github/run-check.sh'), 'spec', 'true'],
                env={**os.environ, 'CI_DIAGNOSTICS_DIR': temporary}, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0)
            self.assertNotIn('::error', result.stdout)



class CaseRunnerTests(unittest.TestCase):
    def test_multiple_failures_do_not_stop_later_cases(self):
        events = []
        captured = io.StringIO()
        with contextlib.redirect_stdout(captured):
            cases = Cases()
            for name, failure in [('first', AssertionError('bad count')), ('second', ValueError('bad JSON')), ('last', None)]:
                with cases.case(name) as enabled:
                    if enabled:
                        events.append(name)
                        if failure:
                            raise failure
            self.assertEqual(events, ['first', 'second', 'last'])
            with self.assertRaises(SystemExit) as stopped:
                cases.finish()
        self.assertEqual(stopped.exception.code, 1)
        summary = json.loads(captured.getvalue().split(SUMMARY_MARKER)[1].splitlines()[0])
        self.assertEqual([r['status'] for r in summary['cases']], ['failed', 'failed', 'passed'])
        self.assertIn('bad count', summary['cases'][0]['traceback'])
        self.assertIn('bad JSON', summary['cases'][1]['traceback'])

    def test_failed_prerequisite_blocks_only_dependents(self):
        events = []
        with contextlib.redirect_stdout(io.StringIO()):
            cases = Cases()
            with cases.case('generation') as enabled:
                if enabled:
                    raise AssertionError('missing bundle')
            with cases.case('dependent', requires=('generation',)) as enabled:
                if enabled:
                    events.append('invalid dependent body')
            with cases.case('unrelated') as enabled:
                if enabled:
                    events.append('unrelated')
            with self.assertRaises(SystemExit):
                cases.finish()
        self.assertEqual(events, ['unrelated'])
        self.assertEqual(cases.results['dependent']['status'], 'blocked')
        self.assertEqual(cases.results['dependent']['prerequisites'], ['generation'])

    def test_nested_trace_failure_keeps_behavior_case_running(self):
        events = []
        with contextlib.redirect_stdout(io.StringIO()):
            cases = Cases(selected=['operation'])
            with cases.case('operation') as enabled:
                if enabled:
                    with cases.case('trace:operation') as trace:
                        if trace:
                            raise AssertionError('source correspondence')
                    events.append('behavior verified')
            with self.assertRaises(SystemExit):
                cases.finish()
        self.assertEqual(events, ['behavior verified'])
        self.assertEqual(cases.results['trace:operation']['status'], 'failed')

    def test_filter_and_empty_filter_do_not_produce_false_success(self):
        with contextlib.redirect_stdout(io.StringIO()):
            cases = Cases(selected=filter(None, ['']))
            with cases.case('default') as enabled:
                self.assertTrue(enabled)
            cases.finish()
            cases = Cases(selected=['typo'])
            with cases.case('real') as enabled:
                self.assertFalse(enabled)
            with self.assertRaises(SystemExit):
                cases.finish()
        self.assertEqual(cases.results['typo']['status'], 'failed')

    def test_real_integration_runner_reaches_later_cases_after_failures(self):
        calls = []
        def command(arguments, **options):
            calls.append(arguments)
            if arguments[1] == 'inspect':
                output = Path(arguments[arguments.index('--output') + 1])
                output.mkdir()
                (output / 'inventory.json').write_text(json.dumps({'resolutions': [{'validation': {'encoding': 'relation'}}]}))
                return subprocess.CompletedProcess(arguments, 0, '', '')
            return subprocess.CompletedProcess(arguments, 2, '', 'controlled generator failure')
        output = io.StringIO()
        arguments = ['integration.py', 'generator', str(REPOSITORY), 'validator', 'java']
        with patch.dict(os.environ, {'AGDA2SYSML_TEST_CASES': 'register,workflow,relational-inspection'}), \
             patch.object(sys, 'argv', arguments), patch.object(subprocess, 'run', side_effect=command), \
             contextlib.redirect_stdout(output):
            with self.assertRaises(SystemExit) as stopped:
                runpy.run_path(str(REPOSITORY / 'test/integration.py'), run_name='__main__')
        self.assertEqual(stopped.exception.code, 1)
        self.assertEqual([arguments[1] for arguments in calls], ['generate', 'generate', 'inspect'])
        summary = json.loads(output.getvalue().split(SUMMARY_MARKER)[1].splitlines()[0])
        statuses = {row['case']: row['status'] for row in summary['cases']}
        self.assertEqual(statuses['register'], 'failed')
        self.assertEqual(statuses['workflow'], 'failed')
        self.assertEqual(statuses['relational-inspection'], 'passed')

    def test_real_evidence_and_completion_checks_preserve_requirements(self):
        tree = ast.parse((REPOSITORY / 'test/integration.py').read_text())
        helpers = [n for n in tree.body if isinstance(n, ast.FunctionDef)
                   and n.name in ('check', 'check_evidence', 'check_completion')]
        namespace = {'sys': sys, 'assertion_failure': lambda *args: None}
        exec(compile(ast.Module(body=helpers, type_ignores=[]), 'integration-checks', 'exec'), namespace)
        evidence = namespace['check_evidence']
        evidence({'comparisons': 101, 'unusedRuntimeInputs': 0, 'preserved': True},
                 {'comparisons': 100, 'unusedRuntimeInputs': 0, 'preserved': True}, 'evidence')
        for actual in ({'comparisons': 99, 'unusedRuntimeInputs': 0, 'preserved': True},
                       {'comparisons': 101, 'unusedRuntimeInputs': 1, 'preserved': True},
                       {'comparisons': 101, 'unusedRuntimeInputs': 0, 'preserved': False},
                       {'comparisons': 101, 'unusedRuntimeInputs': 0, 'preserved': 1}):
            with self.assertRaises(AssertionError):
                evidence(actual, {'comparisons': 100, 'unusedRuntimeInputs': 0, 'preserved': True}, 'evidence')
        completion = namespace['check_completion']
        for complete, status, obligation in [(True, 0, 'discharged'), (False, 2, 'textual')]:
            completion(subprocess.CompletedProcess([], status), {'complete': complete, 'targetValidation': 'accepted'},
                       {'complete': complete, 'obligations': [{'status': obligation}]})
        for status, manifest, report in [
                (0, {'complete': False, 'targetValidation': 'accepted'}, {'complete': False, 'obligations': [{'status': 'textual'}]}),
                (0, {'complete': True, 'targetValidation': 'accepted'}, {'complete': True, 'obligations': [{'status': 'textual'}]}),
                (0, {'complete': True, 'targetValidation': 'rejected'}, {'complete': True, 'obligations': [{'status': 'discharged'}]})]:
            with self.assertRaises(AssertionError):
                completion(subprocess.CompletedProcess([], status), manifest, report)

    def test_selected_case_family_runs_independent_children(self):
        with contextlib.redirect_stdout(io.StringIO()):
            cases = Cases(selected=['payload'])
            with cases.case('payload') as enabled:
                self.assertTrue(enabled)
            with cases.case('payload:provenance', requires=('payload',)) as enabled:
                if enabled:
                    raise AssertionError('missing origins')
            with cases.case('payload:behavior', requires=('payload',)) as enabled:
                self.assertTrue(enabled)
            with self.assertRaises(SystemExit):
                cases.finish()
        self.assertEqual(cases.results['payload:behavior']['status'], 'passed')

    def test_keyboard_interrupt_is_not_swallowed(self):
        with contextlib.redirect_stdout(io.StringIO()):
            cases = Cases()
            with self.assertRaises(KeyboardInterrupt):
                with cases.case('interrupt') as enabled:
                    if enabled:
                        raise KeyboardInterrupt()

    def test_summary_preserves_every_case_and_failure_receipt(self):
        with tempfile.TemporaryDirectory(prefix='ci-report-test-') as temporary:
            directory = Path(temporary)
            (directory / 'integration.exit').write_text('1\n')
            (directory / 'integration.command').write_text('integration runner\n')
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                cases = Cases()
                for name in ('<first>', 'second'):
                    with cases.case(name) as enabled:
                        if enabled:
                            raise AssertionError(name)
                with cases.case('passing') as enabled:
                    self.assertTrue(enabled)
                with self.assertRaises(SystemExit):
                    cases.finish()
            # Simulate both complete producer output and repeated Nix excerpts.
            (directory / 'integration.log').write_text(output.getvalue() + output.getvalue())
            destination = directory / 'job-summary.md'
            summarize(directory, destination)
            summary = destination.read_text()
            self.assertIn('&lt;first&gt;', summary)
            self.assertIn('second', summary)
            self.assertIn('passing', summary)
            self.assertEqual(len(list(directory.glob('integration-failure-*.json'))), 2)
            statuses = json.loads((directory / 'integration-cases.json').read_text())['cases']
            self.assertEqual([r['status'] for r in statuses], ['failed', 'failed', 'passed'])

if __name__ == '__main__':
    unittest.main()
