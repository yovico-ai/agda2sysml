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
from unittest.mock import patch

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

    def test_success_is_not_reported_as_failure(self):
        with tempfile.TemporaryDirectory(prefix='ci-report-test-') as temporary:
            result = subprocess.run(['bash', str(REPOSITORY / '.github/run-check.sh'), 'spec', 'true'],
                env={**os.environ, 'CI_DIAGNOSTICS_DIR': temporary}, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0)
            self.assertNotIn('::error', result.stdout)


if __name__ == '__main__':
    unittest.main()
