#!/usr/bin/env bash
# Keep the command's status, rather than tee's, and retain its complete log.
set -euo pipefail
name=$1
shift
diagnostics_dir=${CI_DIAGNOSTICS_DIR:-ci-diagnostics}
mkdir -p "$diagnostics_dir"
printf '%q ' "$@" > "$diagnostics_dir/$name.command"
printf '\n' >> "$diagnostics_dir/$name.command"
set +e
"$@" 2>&1 | tee "$diagnostics_dir/$name.log"
statuses=("${PIPESTATUS[@]}")
set -e
status=${statuses[0]}
if (( statuses[1] != 0 )); then
  echo "Diagnostic log capture failed: tee exited ${statuses[1]}" >&2
  if (( status == 0 )); then status=${statuses[1]}; fi
fi
printf '%s\n' "$status" > "$diagnostics_dir/$name.exit"
if (( status != 0 )); then
  printf '::error title=%s check failed::Exit %s. See the %s step log and ci-diagnostics artifact.\n' "$name" "$status" "$name"
fi
exit "$status"
