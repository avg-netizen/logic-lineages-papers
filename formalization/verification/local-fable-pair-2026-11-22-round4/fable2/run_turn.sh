#!/usr/bin/env bash
# One Fable-2 turn through the user's claudep wrapper (API credits first, subscription fallback).
# Usage: run_turn.sh NNN [resume-session-id]
set -u
here="$(cd "$(dirname "$0")" && pwd)"; root="$(cd "$here/../../.." && pwd)"
turn="${1:?turn}"; resume="${2:-}"
gate="verification/local-fable-pair-2026-11-22-round4/gate.sh"
args=(--model claude-fable-5-2 --effort high --output-format stream-json --verbose
  --permission-mode dontAsk --strict-mcp-config --mcp-config '{"mcpServers":{}}'
  --tools "Read,Glob,Grep,Edit,Write,Bash"
  --allowedTools "Read" "Glob" "Grep" "Edit" "Write"
    "Bash(bash $gate:*)" "Bash(python3 verification/local-fable-pair-2026-11-22-round4/import_graph.py:*)"
    "Bash(sha256sum:*)" "Bash(ls:*)" "Bash(wc:*)" "Bash(grep:*)" "Bash(cat:*)" "Bash(head:*)"
    "Bash(tail:*)" "Bash(cp:*)" "Bash(mkdir:*)" "Bash(date:*)" "Bash(sed -n:*)" "Bash(find:*)")
[ -n "$resume" ] && args+=(--resume "$resume")
cd "$root" || exit 2
date -u +%FT%TZ > "$here/$turn-started.txt"
/home/other/storage/projects/palace2/.claude/tools/claudep/claudep "${args[@]}" \
  < "$here/$turn-prompt.txt" > "$here/$turn-stream.jsonl" 2> "$here/$turn-stderr.txt"
rc=$?
python3 - "$here" "$turn" "$rc" <<'PY'
import json,sys,pathlib,hashlib,datetime
here=pathlib.Path(sys.argv[1]); turn=sys.argv[2]; rc=int(sys.argv[3])
ev=[]
for l in (here/f"{turn}-stream.jsonl").read_text(errors="replace").splitlines():
    try: ev.append(json.loads(l))
    except ValueError: pass
init=[e for e in ev if e.get("type")=="system" and e.get("subtype")=="init"]
res=[e for e in ev if e.get("type")=="result"]
err=(here/f"{turn}-stderr.txt").read_text(errors="replace")
r={"turn":turn,"exit_code":rc,"ended_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),
   "prompt_sha256":hashlib.sha256((here/f"{turn}-prompt.txt").read_bytes()).hexdigest(),
   "observed_fallback":"retrying on subscription" in err,
   "assistant_events":sum(1 for e in ev if e.get("type")=="assistant")}
if init: r.update(session_id=init[-1].get("session_id"),init_model=init[-1].get("model"),api_key_source=init[-1].get("apiKeySource"))
if res:
    x=res[-1]; r.update(result_type=x.get("subtype"),is_error=x.get("is_error"),session_id=x.get("session_id",r.get("session_id")),
        num_turns=x.get("num_turns"),cost_usd=x.get("total_cost_usd"),usage=x.get("usage"))
    if isinstance(x.get("result"),str): (here/f"{turn}-answer.md").write_text(x["result"]+"\n")
(here/f"{turn}-receipt.json").write_text(json.dumps(r,indent=2)+"\n")
print(json.dumps({k:r.get(k) for k in ["exit_code","session_id","init_model","api_key_source","observed_fallback","result_type","is_error","num_turns","cost_usd"]}))
PY
exit $rc
