"""Launch one authorized Fable turn through the user's API-first wrapper."""
import datetime
import hashlib
import json
import pathlib
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
REPO = HERE.parents[3]
WRAPPER = pathlib.Path("/home/other/storage/projects/palace2/.claude/tools/claudep/claudep")
turn = sys.argv[1] if len(sys.argv) > 1 else "001"
receipt_path = HERE / (turn + "-receipt.json")
receipt = json.loads(receipt_path.read_text())
prompt_path = HERE / (turn + "-prompt.txt")
assert hashlib.sha256(prompt_path.read_bytes()).hexdigest() == receipt["prompt_sha256"]
credential_lines = WRAPPER.with_name(".env").read_text().splitlines()
assert any(line.startswith("ANTHROPIC_CREDITS_KEY=") and line.split("=", 1)[1].strip().strip(chr(34) + chr(39)) for line in credential_lines), "Missing API credential; no silent subscription launch"
args = [str(WRAPPER), "--model", "claude-fable-5-2", "--effort", "high",
        "--output-format", "stream-json", "--verbose", "--tools", "Read,Glob,Grep",
        "--allowedTools", "Read,Glob,Grep", "--permission-mode", "dontAsk",
        "--strict-mcp-config", "--mcp-config", '{"mcpServers":{}}']
if receipt.get("resume_session_id"):
    args += ["--resume", receipt["resume_session_id"]]
receipt.update(status="launching", started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), argv=args)
receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
with prompt_path.open("rb") as prompt, (HERE / (turn + "-stream.jsonl")).open("wb") as out, (HERE / (turn + "-stderr.txt")).open("wb") as err:
    process = subprocess.Popen(args, stdin=prompt, stdout=out, stderr=err, cwd=REPO)
    receipt.update(status="running", pid=process.pid)
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    code = process.wait()
events = []
for line in (HERE / (turn + "-stream.jsonl")).read_text(errors="replace").splitlines():
    try:
        events.append(json.loads(line))
    except ValueError:
        pass
initials = [e for e in events if e.get("type") == "system" and e.get("subtype") == "init"]
results = [e for e in events if e.get("type") == "result"]
responses = [e for e in events if e.get("type") == "assistant" and not e.get("error")]
stderr_text = (HERE / (turn + "-stderr.txt")).read_text(errors="replace")
receipt.update(exit_code=code, ended_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
               observed_fallback="API credits exhausted; retrying on subscription" in stderr_text,
               assistant_response_count=len(responses), init_count=len(initials))
if initials:
    receipt["session_id"] = initials[-1].get("session_id")
    receipt["init_model"] = initials[-1].get("model")
    receipt["api_key_source"] = initials[-1].get("apiKeySource")
if results:
    result = results[-1]
    receipt["result_type"] = result.get("subtype")
    receipt["is_error"] = result.get("is_error")
    receipt["session_id"] = result.get("session_id", receipt.get("session_id"))
    receipt["usage"] = result.get("usage")
    receipt["model_usage"] = result.get("modelUsage")
    receipt["cost_usd"] = result.get("total_cost_usd")
    answer = result.get("result", "")
    if isinstance(answer, str):
        (HERE / (turn + "-answer.md")).write_text(answer + "\n")
success = code == 0 and responses and results and not results[-1].get("is_error")
receipt["status"] = "completed" if success else "failed"
receipt["resumability"] = "genuine successful assistant response and result verified" if success else "not established by this turn"
for suffix in ["stream.jsonl", "stderr.txt"]:
    source = HERE / (turn + "-" + suffix)
    receipt[suffix + "_sha256"] = hashlib.sha256(source.read_bytes()).hexdigest()
receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
print(json.dumps({k: receipt.get(k) for k in ["status", "exit_code", "session_id", "init_model", "api_key_source", "observed_fallback", "assistant_response_count", "resumability"]}))
sys.exit(0 if success else 1)
