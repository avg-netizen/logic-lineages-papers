#!/usr/bin/env bash
# Run the serialized Lean checker (scripts/check.py) on the ThinkPad instead of this host.
#
#   tp.sh status                 remote memory, mains power, toolchain, any running checker
#   tp.sh setup                  one-time: mirror toolchain + pinned package objects (about 9 GB)
#   tp.sh push                   send sources, compiled-object cache and receipts (newer files only)
#   tp.sh gate MODULE [MODULE…]  push, run check.py there (Mathlib profile, same caps), pull
#   tp.sh pull                   bring back new compiled objects, receipts and logs
#
# Why it mirrors absolute paths: check.py's cache key contains the absolute paths of the compiler,
# of LEAN_PATH and of every imported object. With the same user (other), the same paths and the
# same bytes, a module checked on either machine is a cache hit on the other.
#
# Nothing is deleted on either side (no --delete). The remote job runs in a transient systemd user
# scope at nice 19 with a memory ceiling, and only on mains power.
set -u
here_cfg="$(cd "$(dirname "$0")" && pwd -P)/host.local"      # git-ignored: one line, user@address
HOST="${TP_HOST:-$( [ -f "$here_cfg" ] && head -1 "$here_cfg" )}"
[ -n "$HOST" ] || { echo "set TP_HOST or write user@address into verification/remote-thinkpad/host.local" >&2; exit 2; }
SSH=(ssh -F /dev/null -o BatchMode=yes -o ConnectTimeout=8 -o ServerAliveInterval=30)
RSYNC=(rsync -a -e "ssh -F /dev/null -o BatchMode=yes -o ConnectTimeout=8")
here="$(cd "$(dirname "$0")" && pwd -P)"
ROOT="$(cd "$here/../.." && pwd -P)"                 # …/formalization, same absolute path on both hosts
PKG="$(readlink -f "$ROOT/.lake/packages")"          # real directory of the pinned packages
TOOLCHAIN_NAME="$(sed 's#/#--#; s#:#---#' "$ROOT/lean-toolchain")"
ELAN="$HOME/.elan"
MEMORY_MAX="${TP_MEMORY_MAX:-6G}"
CHECK_FLAGS=(--memory-mib 2048 --rss-mib 1536 --min-free-mib 2048)   # identical to the local gate
log="$here/logs/$(date +%Y%m%dT%H%M%S)-$$-${1:-none}.log"

remote() { "${SSH[@]}" "$HOST" "$@"; }

status() {
  remote "echo host=\$(hostname) mains=\$(cat /sys/class/power_supply/AC*/online 2>/dev/null); free -m | sed -n 2p;
          export PATH=\$HOME/.elan/bin:\$PATH; cd '$ROOT' 2>/dev/null && { lean --version 2>&1 | head -1; ls .lake/build/lib/lean 2>/dev/null | head -1; } || echo 'mirror absent';
          pgrep -af 'scripts/check.py' | head -3 || true"
}

setup() {
  remote "mkdir -p '$ROOT/.lake' '$PKG' '$ELAN/toolchains'" || return 1
  echo "== toolchain ($TOOLCHAIN_NAME)"
  "${RSYNC[@]}" -H "$ELAN/bin" "$ELAN/settings.toml" "$ELAN/env" "$HOST:$ELAN/" || return 1
  "${RSYNC[@]}" "$ELAN/toolchains/$TOOLCHAIN_NAME" "$HOST:$ELAN/toolchains/" || return 1
  echo "== pinned package objects (every package directory, compiled objects only)"
  "${RSYNC[@]}" --include='/*/' --include='/*/.lake/' --include='/*/.lake/build/' \
     --include='/*/.lake/build/lib/' --include='/*/.lake/build/lib/lean/***' --exclude='*' \
     "$PKG/" "$HOST:$PKG/" || return 1
  remote "[ -e '$ROOT/.lake/packages' ] || ln -s '$PKG' '$ROOT/.lake/packages'" || return 1
  push || return 1
  status
}

push() {
  remote "mkdir -p '$ROOT/.lake/build' '$ROOT/build-reports'" || return 1
  "${RSYNC[@]}" -u "$ROOT/LogicLineages" "$ROOT/LogicLineages.lean" "$ROOT/scripts" \
     "$ROOT/lean-toolchain" "$ROOT/lake-manifest.json" "$ROOT/lakefile.toml" "$HOST:$ROOT/" || return 1
  "${RSYNC[@]}" -u "$ROOT/.lake/build/" "$HOST:$ROOT/.lake/build/" || return 1
  "${RSYNC[@]}" -u "$ROOT/build-reports/" "$HOST:$ROOT/build-reports/" || return 1
}

pull() {
  "${RSYNC[@]}" -u "$HOST:$ROOT/.lake/build/" "$ROOT/.lake/build/" || return 1
  "${RSYNC[@]}" -u "$HOST:$ROOT/build-reports/" "$ROOT/build-reports/" || return 1
}

gate() {
  [ "$#" -ge 1 ] || { echo "usage: tp.sh gate MODULE [MODULE…]" >&2; return 2; }
  push || return 1
  deadline=$(( $(date +%s) + ${TP_WAIT_SECONDS:-1800} ))
  while :; do
    remote "[ \"\$(cat /sys/class/power_supply/AC*/online 2>/dev/null)\" = 1 ] || { echo THINKPAD_ON_BATTERY; exit 77; }
          export PATH=\$HOME/.elan/bin:\$PATH XDG_RUNTIME_DIR=/run/user/\$(id -u); cd '$ROOT' || exit 78
          systemd-run --user --scope --quiet -p MemoryMax=$MEMORY_MAX -p CPUWeight=20 \
            nice -n 19 python3 scripts/check.py ${CHECK_FLAGS[*]} $*"
    rc=$?
    # 75 = another checker holds the remote lock, 76 = remote free-memory floor closed: wait and retry
    if [ "$rc" -ne 75 ] && [ "$rc" -ne 76 ]; then break; fi
    if [ "$(date +%s)" -ge "$deadline" ]; then echo "REMOTE_WAIT_TIMEOUT rc=$rc" >&2; break; fi
    sleep $(( rc == 76 ? 20 : 4 ))
    push || break                                   # pick up sources another lane changed meanwhile
  done
  pull || echo "PULL_FAILED (results remain on $HOST under $ROOT)" >&2
  echo "REMOTE_GATE host=$HOST rc=$rc"
  return $rc
}

cmd="${1:-status}"; shift || true
case "$cmd" in
  status|setup|push|pull|gate) "$cmd" "$@" 2>&1 | tee "$log"; exit "${PIPESTATUS[0]}" ;;
  *) echo "unknown command: $cmd" >&2; exit 2 ;;
esac
