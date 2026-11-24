#!/usr/bin/env python3
"""Check the current register and bounded cross-branch evidence; never invokes Lean."""
from collections import Counter
from hashlib import sha1, sha256
from pathlib import Path
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
FORM = ROOT / "formalization"
VERIFY = FORM / "verification/new-paper-set-2026-11-18"
LIVE = VERIFY / "accepted"
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
NUMBERED = "current numbered statement"


def load(path):
    return json.loads(path.read_text())


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def content_id(path):
    body = path.read_bytes()
    return sha1(b"blob " + str(len(body)).encode() + b"\0" + body).hexdigest()


def verify_link_fields(record, is_retired=False):
    if "evidence" in record:
        assert digest(VERIFY / record["evidence"]) == record["evidence_sha256"], record["id"]
    else:
        assert record["kind"] == NUMBERED and record.get("supporting_record"), record["id"]
    for p, h in record.get("source_pins", {}).items():
        assert digest(ROOT / p) == h, (record["id"], p)
    for field in ("statement_scope_check", "source_map", "freeze"):
        if field in record:
            assert (VERIFY / record[field]).is_file(), (record["id"], field)
    if "supporting_record" in record:
        p = LIVE / record["supporting_record"]
        assert p.is_file(), record["id"]
        if "supporting_record_sha256" in record:
            assert digest(p) == record["supporting_record_sha256"], record["id"]
    for support in record.get("supporting_records", []):
        assert (LIVE / support).is_file(), (record["id"], support)
    if "standard_axioms" in record:
        assert set(record["standard_axioms"]) <= AXIOMS, record["id"]
    assert is_retired or record["kind"] == NUMBERED or not record.get("numbered_promotions"), record["id"]


def main():
    index = load(HERE / "INDEX.json")
    archive = load(ROOT / "archive/comparison-editions-pre-2026-11-17/MANIFEST.json")
    for row in archive["files"]:
        for key in ("original_path", "archived_path"):
            p = ROOT / row[key]
            assert p.stat().st_size == row["bytes"] and digest(p) == row["sha256"], row[key]

    reg = load(FORM / "CURRENT-COMPARISON-TARGETS.json")
    rows = {}
    for paper in reg["papers"]:
        declared = {}
        for source in paper["source_files"]:
            p = ROOT / source["path"]
            assert digest(p) == source["sha256"], source
            tex = p.read_text()
            for m in re.finditer(r"\\begin\{(theorem|lemma|proposition|corollary)\}(.*?)\\end\{\1\}", tex, re.S):
                kind, body = m.groups()
                label = re.search(r"\\label\{([^}]+)\}", body)
                assert label is not None, p
                key = f"{paper['paper']}:{label[1]}"
                assert key not in declared, key
                declared[key] = (kind, body.strip(), tex[:m.start()].count("\n") + 1, source["path"])
        assert len(declared) == paper["numbered_statement_count"]
        assert set(declared) == {r["id"] for r in paper["statements"]}, paper["paper"]
        for r in paper["statements"]:
            key = r["id"]
            assert key not in rows, key
            assert declared[key] == tuple(r[k] for k in ("kind", "statement_latex", "line", "file")), key
            rows[key] = r
    assert len(rows) == reg["numbered_statement_count"]
    count = dict(Counter(row["status"] for row in rows.values()))
    assert count == reg["status_counts"] == index["current_numbered_counts"], count

    ids, live_numbered = {}, {}
    for path in sorted(LIVE.glob("*.json")):
        packet = load(path)
        rid = packet["id"]
        assert rid not in ids, (rid, ids.get(rid), path)
        ids[rid] = path
        assert packet["kind"] in (NUMBERED, "supporting only"), path
        verify_link_fields(packet)
        if packet["kind"] == NUMBERED:
            key = packet["statement"]
            assert key not in live_numbered, key
            live_numbered[key] = (path, packet)
    checked = {k: r for k, r in rows.items() if r["status"] == "checked"}
    assert checked.keys() == live_numbered.keys(), "checked/numbered record bijection"
    for key, row in checked.items():
        p, packet = live_numbered[key]
        assert FORM / row["acceptance"] == p, key
        assert row["formal_target"] == packet["target"] and row["verified_alias"] == packet["exact_alias"], key

    retired = {}
    for key, item in index["retired_current_adoptions"].items():
        assert rows[key]["status"] == "pending" and key not in live_numbered, key
        p = ROOT / item["historical_path"]
        assert not (ROOT / item["original_path"]).exists(), key
        assert digest(p) == item["sha256"], key
        packet = load(p)
        assert packet["kind"] == NUMBERED and packet["statement"] == key and packet["id"] not in ids, key
        verify_link_fields(packet, is_retired=True)
        retired[packet["id"]] = item["original_path"]
    assert set(index["collisions"]) == {f"new-set-{i}" for i in range(1430, 1495)}
    for rid, paths in index["collisions"].items():
        newer = retired[rid] if rid in retired else str(ids[rid].relative_to(ROOT))
        assert paths["newer_path"] == newer, rid
        assert not (ROOT / paths["older_path"]).exists(), rid
    for p, h in index["imported_older_paths_git_blob"].items():
        assert content_id(ROOT / p) == h, p
    for rid, sample in index["selected_older_support"].items():
        path = ROOT / sample["acceptance"]
        assert ids[rid] == path
        packet = load(path)
        assert packet["kind"] == "supporting only", rid
        receipt = load(VERIFY / packet["evidence"])
        assert receipt["status"] == "checked", rid
        assert receipt["exact_gate"] == sample["exact_gate"], rid
        assert receipt["native_receipt"] == packet["native_receipt"] == sample["prior_receipt"], rid
        assert receipt["native_receipt_sha256"] == sample["prior_receipt_sha256"], rid
        assert receipt["named_axiom_output"] == sample["axioms"], rid
        assert len(sample["axioms"]) == packet["exact_alias_count"], rid
        assert all(set(x) <= AXIOMS for x in sample["axioms"].values()), rid
    inherited = index["retained_newer_numbered_evidence"]
    for rid, item in inherited.items():
        acceptance = ROOT / item["acceptance"]
        assert ids[rid] == acceptance, rid
        packet = load(acceptance)
        assert packet["kind"] == NUMBERED, rid
        supporting = load(LIVE / packet["supporting_record"]) if "supporting_record" in packet else {}
        linked = dict(supporting, **packet)
        ep = ROOT / item["native_evidence"]
        assert ep == (VERIFY / linked["evidence"]).resolve(), rid
        assert digest(ep) == linked["evidence_sha256"] == item["evidence_sha256"], rid
        receipt = load(ep)
        assert receipt["status"] == "checked", rid
        assert (receipt.get("exact_gate") or receipt["native_module"]) == item["exact_gate"], rid
        assert receipt["native_receipt"] == packet["native_receipt"] == item["native_receipt"], rid
        assert receipt["native_receipt_sha256"] == item["native_receipt_sha256"], rid
        assert all(set(xs) <= AXIOMS for xs in receipt["named_axiom_output"].values()), rid
        overrides = item["historical_source_pin_overrides"]
        assert overrides.keys() <= receipt["source_pins"].keys(), rid
        for path, expected in receipt["source_pins"].items():
            if path not in overrides:
                assert digest(ROOT / path) == expected, (rid, path)
            else:
                override = overrides[path]
                archived = ROOT / override["archived_path"]
                assert digest(archived) == expected, (rid, path)
                assert digest(ROOT / path) == override["current_sha256"], (rid, path)
                assert (ROOT / path).read_bytes()[:override["prefix_bytes"]] == archived.read_bytes(), (rid, path)
    print(json.dumps({"archive_pairs": len(archive["files"]), "numbered_status": count,
                      "current_acceptance_ids": len(ids), "historical_adoptions": len(retired),
                      "branch_local_identifier_collisions": len(index["collisions"]),
                      "imported_older_paths": len(index["imported_older_paths_git_blob"]),
                      "checked_support_receipt_metadata": len(index["selected_older_support"]),
                      "retained_numbered_receipt_metadata": len(inherited),
                      "verification": "static only; not a full build or re-audit of historical acceptance decisions"}, indent=2))


if __name__ == "__main__":
    main()
