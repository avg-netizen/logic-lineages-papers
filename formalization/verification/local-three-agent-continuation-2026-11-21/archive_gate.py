"""Archive a scoped, successful current receipt and its independently replayable sources/objects."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
VERIFY = ROOT / "verification/local-two-sol-2026-11-18/root_verify.py"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("key")
    parser.add_argument("module")
    parser.add_argument("receipt")
    parser.add_argument("log", type=Path)
    parser.add_argument("--alias", action="append", default=[])
    parser.add_argument("--alias-namespace")
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Z0-9-]+", args.key):
        parser.error("Expected uppercase packet identifier")
    gate = ROOT / "build-reports" / (args.receipt + ".json")
    record = json.loads(gate.read_text())
    assert record["requested"] == [args.module] and "outcome" not in record
    assert all(row.get("returncode") == 0 for row in record["modules"])
    compiler = Path(shutil.which("lean"))
    prefix = subprocess.check_output([str(compiler), "--print-prefix"], cwd=ROOT, text=True).strip()
    with tempfile.TemporaryDirectory() as temp:
        audit = Path(temp) / "source-object-audit.json"
        command = ["python3", str(VERIFY), args.module, "--out", str(audit),
                   "--audit-prefix", args.module, "--compiler", str(compiler),
                   "--compiler-prefix", prefix]
        for alias in args.alias:
            command.extend(["--require-audit", (args.alias_namespace or args.module) + "." + alias])
        subprocess.run(command, check=True, cwd=ROOT, stdout=subprocess.DEVNULL)
        result = json.loads(audit.read_text())
        assert result["status"] == "verified" and not result["errors"]
        rows = {r["module"]: r for r in record["modules"]}
        assert rows.keys() == result["modules"].keys()
        archive = HERE / (args.key.lower() + "-native") / "verified-native-closure.zip"
        archive.parent.mkdir(exist_ok=True)
        assert not archive.exists()
        with zipfile.ZipFile(archive, "x", compression=zipfile.ZIP_DEFLATED) as out:
            out.write(gate, "receipt.json")
            out.write(args.log, "gate.log")
            out.write(audit, audit.name)
            for mod, row in rows.items():
                path = ROOT / row["log"]
                assert digest(path) == result["modules"][mod]["log_sha256"]
                out.write(path, "logs/" + path.name)
        evidence = {k: result[k] for k in ("status", "gates", "native_source_matched_modules",
                                          "errors", "new_named_standard_axioms")}
        evidence.update(native_receipt=args.receipt, native_receipt_sha256=digest(gate),
                        archive=str(archive.relative_to(ROOT)), archive_sha256=digest(archive))
        path = HERE / (args.key + "-LOCAL-EVIDENCE.json")
        path.write_text(json.dumps(evidence, indent=2) + "\n")
        print(args.key, len(rows), digest(path))


if __name__ == "__main__":
    main()
