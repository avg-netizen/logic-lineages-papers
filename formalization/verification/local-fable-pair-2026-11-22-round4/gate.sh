#!/usr/bin/env bash
# Serialized native gate for the local three-party continuation.
# Usage: gate.sh core|mathlib MODULE [MODULE...]
#   core    -> python3 scripts/check.py --core-profile ...            (paper16 / Init-Lean-Std closures)
#   mathlib -> python3 scripts/check.py --memory-mib 2048 --rss-mib 1536 --min-free-mib 2048 ...
# scripts/check.py, its caps, locks and pins are unchanged. This wrapper only
# waits politely when the single compiler lock is busy (exit 75) or the memory
# gate is closed (exit 76), and raises a flag so the background cache warmer yields.
set -u
here="$(cd "$(dirname "$0")" && pwd)"; root="$(cd "$here/../.." && pwd)"
profile="${1:?profile}"; shift
case "$profile" in
  core) flags=(--core-profile) ;;
  mathlib) flags=(--memory-mib 2048 --rss-mib 1536 --min-free-mib 2048) ;;
  *) echo "profile must be core or mathlib" >&2; exit 2 ;;
esac
flag="$here/logs/gate-waiting.$$"; : > "$flag"; trap 'rm -f "$flag"' EXIT
cd "$root" || exit 2
deadline=$(( $(date +%s) + ${GATE_WAIT_SECONDS:-1500} ))
while :; do
  touch "$flag"
  python3 scripts/check.py "${flags[@]}" "$@"; rc=$?
  if [ "$rc" -ne 75 ] && [ "$rc" -ne 76 ]; then exit "$rc"; fi
  if [ "$(date +%s)" -ge "$deadline" ]; then echo "GATE_WAIT_TIMEOUT rc=$rc" >&2; exit "$rc"; fi
  sleep $(( rc == 76 ? 20 : 3 ))
done
