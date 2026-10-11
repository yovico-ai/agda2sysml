"""CI reporting only; standard library, no production dependencies."""
import html
import json
import os
from pathlib import Path
import shlex
import sys

MARKER = 'AGDA2SYSML_CI_FAILURE '
CASE_SUMMARY_MARKER = 'AGDA2SYSML_CI_CASES '


def command_failure(command, expected, result, output):
    """Read small diagnostic files before the generated temporary bundle goes away."""
    details = {'command': command, 'cwd': os.getcwd(), 'expectedExit': expected,
               'actualExit': result.returncode, 'stdout': result.stdout, 'stderr': result.stderr}
    for filename in ('manifest.json', 'diagnostics.json'):
        path = Path(output) / filename
        try:
            value = json.loads(path.read_text())
            if filename == 'manifest.json':
                value = {k: value.get(k) for k in ('complete', 'targetValidation', 'selectionProfile', 'entryModules')}
            details[filename] = value
        except (OSError, ValueError) as error:
            details[filename] = {'unavailable': str(error)}
    print(MARKER + json.dumps(details), flush=True)
    return (f"Command: {shlex.join(command)}\nExpected exit {expected}; actual exit {result.returncode}\n"
            f"Diagnostics: {json.dumps(details.get('diagnostics.json'), ensure_ascii=False)}\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}")


def assertion_failure(message, context):
    details = {'assertion': message, 'evidence': {name: value for name, value in context.items()
               if name.endswith('_evidence') and isinstance(value, dict)},
               'counts': {name: len(context[name]) for name in ('instances', 'problems', 'textual', 'own')
                          if name in context and isinstance(context[name], (list, dict, set))}}
    print(MARKER + json.dumps(details), flush=True)


def summarize(directory, destination):
    directory = Path(directory)
    lines = ['## CI checks', '', '| Check | Result |', '| --- | --- |']
    failures = []
    for name in ('reporting', 'spec', 'generator', 'validator', 'integration'):
        exit_file = directory / (name + '.exit')
        status = exit_file.read_text().strip() if exit_file.exists() else None
        result = 'Passed' if status == '0' else f'Failed (exit {status})' if status else 'Not run'
        if name == 'integration' and status is None:
            blocked = [dependency for dependency in ('generator', 'validator')
                       if (directory / (dependency + '.exit')).exists()
                       and (directory / (dependency + '.exit')).read_text().strip() != '0']
            if blocked:
                result = 'Blocked by failed ' + ', '.join(blocked)
        lines.append(f'| {name} | {result} |')
        if status and status != '0':
            failures.append((name, status))
    integration_log = directory / 'integration.log'
    if integration_log.exists():
        summaries = []
        for row in integration_log.read_text(errors='replace').splitlines():
            if CASE_SUMMARY_MARKER in row:
                try:
                    summary = json.loads(row.split(CASE_SUMMARY_MARKER, 1)[1])
                    if isinstance(summary.get('cases'), list):
                        summaries.append(summary)
                except (ValueError, AttributeError):
                    pass
        if summaries:
            summary = summaries[-1]
            (directory / 'integration-cases.json').write_text(json.dumps(summary, indent=2) + '\n')
            lines += ['', '### Integration cases', '', '| Case | Result | Seconds |', '| --- | --- | --- |']
            for case in summary['cases']:
                label = html.escape(str(case.get('case', '?'))).replace('|', '&#124;')
                result = html.escape(str(case.get('status', '?')))
                lines.append(f"| {label} | {result} | {case.get('seconds', '')} |")
    for name, status in failures:
        command = (directory / (name + '.command')).read_text().strip()
        lines += ['', f'### {name}: exit {status}', '', '<pre>' + html.escape(command) + '</pre>']
        log = (directory / (name + '.log')).read_text(errors='replace')
        receipts = []
        for row in log.splitlines():
            if MARKER in row:
                try:
                    receipt = json.loads(row.split(MARKER, 1)[1])
                    if receipt not in receipts:
                        receipts.append(receipt)
                except ValueError:
                    pass
        for index, receipt in enumerate(receipts):
            (directory / f'{name}-failure-{index + 1}.json').write_text(json.dumps(receipt, indent=2, ensure_ascii=False) + '\n')
            concise = {k: v for k, v in receipt.items() if k not in ('stdout', 'stderr')}
            rendered = json.dumps(concise, indent=2, ensure_ascii=False)
            if len(rendered) > 16000:
                rendered = rendered[:16000] + '\n... Summary shortened; complete details in failure JSON.'
            lines += ['', '<pre>' + html.escape(rendered) + '</pre>']
        # Full logs are retained; this is only the bounded on-screen excerpt.
        rows = [row for row in log.splitlines() if MARKER not in row]
        errors = [row for row in rows if any(token in row for token in
                  ('error:', 'Error:', 'AssertionError', 'Traceback', ' FAIL', 'Exception:'))]
        if errors:
            lines += ['', 'Error lines (complete context in the log):', '<pre>' + html.escape('\n'.join(errors)[:12000]) + '</pre>']
        excerpt = '\n'.join(rows[-60:])[-12000:]
        lines += ['', '<details><summary>Log excerpt (full log in artifact)</summary>',
                  '<pre>' + html.escape(excerpt) + '</pre>', '</details>']
    lines += ['', 'Download **ci-diagnostics** for complete logs, command lines, exit statuses, and failure JSON.',
              'Generated models and correspondence bundles are excluded.', '']
    text = '\n'.join(lines)
    (directory / 'summary.md').write_text(text)
    with Path(destination).open('a') as stream:
        stream.write(text)


if __name__ == '__main__':
    summarize(sys.argv[1], sys.argv[2])
