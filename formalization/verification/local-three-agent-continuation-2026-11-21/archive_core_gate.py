"""Package a source-matched core-only gate using this release's machine limits."""
import argparse
from hashlib import sha256
from importlib.util import module_from_spec, spec_from_file_location
import json
from pathlib import Path
from zipfile import ZIP_DEFLATED, ZipFile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
VERIFIER = ROOT / "verification/local-two-sol-2026-11-18/A/verify_evidence.py"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("key")
    parser.add_argument("receipt")
    parser.add_argument("log", type=Path)
    parser.add_argument("aliases", nargs="+")
    args = parser.parse_args()
    spec = spec_from_file_location("core_checker", VERIFIER)
    checker = module_from_spec(spec)
    spec.loader.exec_module(checker)
    checker.CORE_PROFILE = dict(checker.CORE_PROFILE, heap_cap_mib=2048, minimum_free_mib=2048)
    gate = ROOT / "build-reports" / (args.receipt + ".json")
    report = checker.verify(gate, args.aliases, [])
    record = json.loads(gate.read_text())
    archive = HERE / (args.key.lower() + "-native") / "verified-native-closure.zip"
    archive.parent.mkdir(exist_ok=True)
    with ZipFile(archive, "x", ZIP_DEFLATED) as output:
        output.write(gate, "receipt.json")
        output.write(args.log, "gate.log")
        output.writestr("source-object-audit.json", json.dumps(report, indent=2))
        for row in report["recursive_modules"].values():
            log = ROOT / row["log"]
            output.write(log, "logs/" + log.name)
    evidence = dict(status="verified", gates=record["requested"], errors=[],
                    native_source_matched_modules=len(report["recursive_modules"]),
                    new_named_standard_axioms=report["exact_aliases"], profile=report["profile"],
                    native_receipt=args.receipt, native_receipt_sha256=report["gate_sha256"],
                    archive=str(archive.relative_to(ROOT)), archive_sha256=sha256(archive.read_bytes()).hexdigest())
    (HERE / (args.key + "-LOCAL-EVIDENCE.json")).write_text(json.dumps(evidence, indent=2) + "\n")


if __name__ == "__main__":
    main()
