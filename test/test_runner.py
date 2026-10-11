"""Collect independent integration cases without masking failed prerequisites."""
from contextlib import contextmanager
import json
import time
import traceback

from ci_diagnostics import MARKER

SUMMARY_MARKER = 'AGDA2SYSML_CI_CASES '


class Cases:
    def __init__(self, selected=None):
        self.selected = set(selected or ()) or None
        self.results = {}
        self.active = []

    @contextmanager
    def case(self, name, requires=()):
        if name in self.results:
            raise ValueError('duplicate test case: ' + name)
        selected = (self.selected is None or name in self.selected or bool(self.active)
                    or any(name.startswith(root + ":") or root.startswith(name + ":")
                           for root in self.selected))
        missing = [dependency for dependency in requires
                   if self.results.get(dependency, {}).get('status') != 'passed']
        result = {'case': name, 'status': 'running'}
        self.results[name] = result
        if not selected:
            result['status'] = 'not-selected'
            yield False
            return
        if missing:
            result.update(status='blocked', prerequisites=missing)
            print(MARKER + json.dumps(result), flush=True)
            yield False
            return
        started = time.monotonic()
        self.active.append(name)
        print('CASE ' + name, flush=True)
        try:
            yield True
        except Exception as error:
            result.update(status='failed', exception=type(error).__name__, message=str(error),
                          traceback=traceback.format_exc())
            print(MARKER + json.dumps(result), flush=True)
        else:
            result['status'] = 'passed'
        finally:
            self.active.pop()
            result['seconds'] = round(time.monotonic() - started, 3)
            print(result['status'].upper() + ' ' + name, flush=True)

    def finish(self):
        missing = (self.selected or set()) - self.results.keys()
        for name in sorted(missing):
            self.results[name] = {'case': name, 'status': 'failed', 'message': 'unknown selected case'}
        results = list(self.results.values())
        print(SUMMARY_MARKER + json.dumps({'cases': results}), flush=True)
        failures = [result for result in results if result['status'] in ('failed', 'blocked')]
        print(f"Test cases: {sum(r['status'] == 'passed' for r in results)} passed, "
              f"{sum(r['status'] == 'failed' for r in results)} failed, "
              f"{sum(r['status'] == 'blocked' for r in results)} blocked", flush=True)
        if failures:
            raise SystemExit(1)
