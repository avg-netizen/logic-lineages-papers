#!/usr/bin/env python3
"""Check the saved R001 evidence and current sources; does not launch Lean."""
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read(name):
    raw = (HERE / name).read_bytes()
    return json.loads(gzip.decompress(raw) if name.endswith(".gz") else raw)


def main():
    for encoding in read("EVIDENCE-ENCODINGS.json"):
        raw = (HERE / encoding["path"]).read_bytes()
        assert sha(raw) == encoding["stored_sha256"], encoding["path"]
        assert sha(gzip.decompress(raw)) == encoding["uncompressed_sha256"], encoding["path"]
    acceptance = read("ACCEPTANCE.json")
    pins = read("SOURCE-PINS.json.gz")
    coverage = {row["module"]: row for row in read("SOURCE-NATIVE-COVERAGE.json.gz")["modules"]}
    assert len(pins) == len(coverage) == acceptance["current_native_source_closure"]
    for pin in pins:
        digest = sha((REPO / pin["path"]).read_bytes())
        row = coverage[pin["module"]]
        assert digest == pin["sha256"] == row["source_sha256"], pin["path"]
        assert row["returncode"] == 0, pin["module"]
    frozen = read("FROZEN-SOURCE-PINS.json.gz")
    for pin in frozen:
        assert sha((REPO / pin["path"]).read_bytes()) == pin["sha256"], pin["path"]
    assert len(frozen) == acceptance["frozen_pre_author_pins_checked"]
    audit = read("AXIOMS.json")
    allowed = set(acceptance["allowed_axioms"])
    assert audit["candidate_audit_count"] == 8 and audit["exact_alias_audit_count"] == 2
    for row in audit["candidate_namespace_audit"] + audit["independent_gate_printed_axioms"]:
        assert set(row["actual_axioms"]) <= allowed, row["theorem"]
    assert sha((HERE / "candidate-native-pass.log").read_bytes()) == audit["candidate_log_sha256"]
    assert sha((HERE / "exact-checks.log").read_bytes()) == audit["gate_log_sha256"]
    register = json.loads((REPO / "formalization/TARGETS.json").read_text())
    statuses = Counter(s["status"] for p in register["papers"] for s in p["statements"])
    assert statuses == {"checked": 171, "existing-calculator-package": 2, "pending": 16}
    parent = next(s for p in register["papers"] for s in p["statements"]
                  if s["id"] == "06-godel-t-termination-ordering:lem:id1")
    assert parent["status"] == "pending"
    assert any(c.get("gate_module") == acceptance["gate_module"] for c in parent["checked_components"])
    print(json.dumps({"evidence_verified": True, "native_source_hashes": len(pins),
                      "frozen_pins": len(frozen), "exact_contracts": 2,
                      "candidate_theorems_audited": 8, "numbered_pending": 16,
                      "fresh_Lean_run": False}))


if __name__ == "__main__":
    main()
