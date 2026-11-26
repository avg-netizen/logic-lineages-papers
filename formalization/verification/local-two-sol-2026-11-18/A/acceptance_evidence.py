#!/usr/bin/env python3
"""Export reconciled Lane A evidence in the acceptance register's schema."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None


def export(report):
    assert report["status"] == "source-matched"
    gate = ROOT / report["gate"]
    assert digest(gate) == report["gate_sha256"], gate
    modules = []
    for name, row in report["recursive_modules"].items():
        source = ROOT / (name.replace(".", "/") + ".lean")
        native_receipt = ROOT / row["native_receipt"]
        log = ROOT / row["log"]
        assert digest(source) == row["source_sha256"], source
        assert digest(log) == row["log_sha256"], log
        receipt_sha256 = digest(native_receipt)
        assert receipt_sha256, native_receipt
        outputs = {str(ROOT / path): value for path, value in row["objects"].items()}
        for path, value in outputs.items():
            assert digest(Path(path)) == value, path
        modules.append({
            "module": name,
            "source": str(source),
            "source_sha256": row["source_sha256"],
            "outputs": outputs,
            "native_receipt": str(native_receipt),
            "receipt_sha256": receipt_sha256,
            "log": str(log),
            "log_sha256": row["log_sha256"],
            "input_key": row["input_key"],
            "peak_rss_kib": row["peak_rss_kib"],
        })
    for path, value in report["frozen_sources"].items():
        assert digest(ROOT.parent / path) == value, path
    return {
        "status": "verified",
        "local_modules": len(modules),
        "exact_aliases": len(report["exact_aliases"]),
        "profile": report["profile"],
        "errors": [],
        "source_pins": report["frozen_sources"],
        "axioms": report["exact_aliases"],
        "modules": modules,
        "context": report["compiler"],
        "gate": str(gate),
        "gate_sha256": report["gate_sha256"],
        "full_root_build": False,
        "CI": False,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("evidence", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    result = export(json.loads(args.evidence.read_text()))
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(f"{digest(args.output)}  {args.output}")


if __name__ == "__main__":
    main()
