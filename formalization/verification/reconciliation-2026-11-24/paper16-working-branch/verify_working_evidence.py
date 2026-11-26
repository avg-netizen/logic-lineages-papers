#!/usr/bin/env python3
"""Verify the checked-in Paper 16 focused evidence without running Lean.

This validates exact sources, named axiom output and receipt provenance. It
does not replace a fresh compilation or claim that whole-repository CI passed.
"""

import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys
import tarfile
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
MAX_FILE = 16 * 1024 * 1024
MAX_TOTAL = 128 * 1024 * 1024
RECEIPT_ID = re.compile(r"[0-9]+-[0-9]+\Z")
MODULE = re.compile(r"LogicLineages\.[A-Za-z0-9_]+(?:\.[A-Za-z0-9_]+)*\Z")


def check(good, why):
    if not good:
        raise ValueError(why)


def digest(blob):
    return hashlib.sha256(blob).hexdigest()


def safe_member(name):
    path = PurePosixPath(name)
    check(not path.is_absolute() and ".." not in path.parts and len(path.parts) == 2,
          f"unsafe archive member: {name}")
    check(path.parts[0] in {"build-reports", "failed-drafts", "failed-source", "failed-sources"},
          f"unexpected archive directory: {name}")
    return str(path)


def read_bundle(path):
    payloads = {}
    total = 0

    def add(name, size, read):
        nonlocal total
        name = safe_member(name)
        check(name not in payloads, f"duplicate archive member: {name}")
        check(0 <= size <= MAX_FILE and total + size <= MAX_TOTAL, f"oversize archive member: {name}")
        blob = read()
        check(len(blob) == size, f"truncated archive member: {name}")
        payloads[name] = blob
        total += size

    if path.suffix == ".zip":
        with zipfile.ZipFile(path) as archive:
            for item in archive.infolist():
                check(not item.is_dir(), f"non-file archive member: {item.filename}")
                add(item.filename, item.file_size, lambda: archive.read(item))
    else:
        with tarfile.open(path, "r:xz") as archive:
            for item in archive:
                check(item.isfile(), f"non-file archive member: {item.name}")
                add(item.name, item.size, lambda: archive.extractfile(item).read())
    return payloads


def named_axioms(log):
    text = log.decode("utf-8")
    result = {name.split(".")[-1]: sorted(part.strip() for part in value.split(",") if part.strip())
              for name, value in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", text, re.S)}
    result.update({name.split(".")[-1]: [] for name in
                   re.findall(r"'([^']+)' does not depend on any axioms", text)})
    check(all(set(value) <= ALLOWED for value in result.values()), "unexpected axiom dependency")
    return result


def source_module(name):
    path = PurePosixPath(name)
    check(path.parts[:2] == ("formalization", "LogicLineages") and ".." not in path.parts
          and path.suffix == ".lean", f"unexpected source: {name}")
    module = ".".join(path.with_suffix("").parts[1:])
    check(MODULE.fullmatch(module), f"unexpected module: {module}")
    return module


def row_map(doc):
    rows = doc["modules"]
    mapped = {row["module"]: row for row in rows}
    check(len(rows) == len(mapped), "duplicate module row")
    check(doc["single_thread"] is True and doc["heap_cap_mib"] == 2048
          and doc["rss_cap_mib"] == 1536, "unexpected pinned resource profile")
    return mapped


def receipt_blob(members, rid):
    check(RECEIPT_ID.fullmatch(rid), f"bad receipt ID: {rid}")
    return members[f"build-reports/{rid}.json"]


def package(manifest):
    data = json.loads(manifest.read_text())
    historical = "source_sha256" in data
    if historical:
        envelope = data["receipt"]
        bundle_name = "structural-call-native.zip"
        bundle_sha = envelope["bundle_sha256"]
        rid = envelope["id"]
        length = envelope["fresh_closure_rows"]
        receipt_meta = {rid: {"sha256": envelope["sha256"], "failed_rows": 0}}
        sources = {path: {"source_sha256": row["sha256"], "actual_compile_receipt": rid}
                   for path, row in data["source_sha256"].items()}
        check(set(data["standalone_standard_axioms"]) <= ALLOWED, "unexpected structural foundation")
        paper = data["paper"]
        check(paper["path"] == "16-persistent-marking-termination-ordering/sections/decision.tex",
              "unexpected structural manuscript path")
        check(digest((ROOT / paper["path"]).read_bytes()) == paper["sha256"], "structural source pin differs")
    else:
        bundle_name = data.get("bundle_file") or data["bundle"]
        bundle_sha = data["bundle_sha256"]
        rid = data.get("combined_receipt") or data.get("last_exact_gate_receipt") or data["combined_gate"]
        length = data.get("closure_rows")
        receipt_meta = data["receipts"]
        check(data.get("numbered_promotion", False) is False, "unexpected numbered claim")
        if "sources" in data:
            sources = data["sources"]
        else:
            sources = {
                row.get("path", key): {
                    "source_sha256": row["sha256"],
                    "actual_compile_receipt": row.get("compiled_receipt") or row["compiled_row_receipt"],
                    "axioms": row["axioms"],
                    **({"log": row["log"]} if "log" in row else {}),
                }
                for key, row in data["fresh_source_rows"].items()
            }

    check(bundle_name in {f"{manifest.stem}-native.zip", f"{manifest.stem}-native.tar.xz"},
          "unexpected archive path")
    bundle = HERE / bundle_name
    check(digest(bundle.read_bytes()) == bundle_sha, "archive digest differs")
    members = read_bundle(bundle)

    receipts = {}
    for receipt_id, meta in receipt_meta.items():
        content = receipt_blob(members, receipt_id)
        check(digest(content) == meta["sha256"], f"receipt digest differs: {receipt_id}")
        rows = row_map(json.loads(content))
        fails = sum(row.get("returncode", 1) != 0 for row in rows.values())
        check(fails == meta.get("failed_rows", meta.get("failed_rows_in_receipt", fails)),
              f"receipt failure count differs: {receipt_id}")
        check(len(rows) == meta.get("closure_rows", len(rows)), f"receipt closure differs: {receipt_id}")
        receipts[receipt_id] = rows

    final = receipts[rid]
    check(all(row["returncode"] == 0 for row in final.values()), "combined gate contains a failed module")
    if length is not None:
        check(len(final) == length, "combined closure size differs")

    decl_count = 0
    omitted_logs = 0
    for path, meta in sources.items():
        module = source_module(path)
        source = (ROOT / path).read_bytes()
        expected = meta["source_sha256"]
        check(digest(source) == expected, f"source digest differs: {path}")
        fresh_id = meta["actual_compile_receipt"]
        fresh = receipts[fresh_id][module]
        combined = final[module]
        check(fresh["returncode"] == 0 and "verified_from" not in fresh and
              fresh["source_sha256"] == expected, f"not an exact fresh proof row: {module}")
        check(combined["source_sha256"] == expected and fresh["log"] == combined["log"],
              f"combined row is not the same proof: {module}")
        if combined.get("status") == "verified-cache-hit":
            check(PurePosixPath(combined["verified_from"]).stem == fresh_id, f"wrong cache source: {module}")
        else:
            check(fresh_id == rid and "verified_from" not in combined, f"wrong fresh source: {module}")

        log_path = str(PurePosixPath(fresh["log"]))
        if log_path in members:
            output = named_axioms(members[log_path])
        else:
            check(historical, f"missing axiom log: {module}")
            # The original structural zip preserved only three named logs.
            omitted_logs += 1
            continue
        if "log" in meta:
            check(log_path == meta["log"], f"log path differs: {module}")
        if "axioms" in meta:
            check(output == {name: sorted(value) for name, value in meta["axioms"].items()},
                  f"named axiom output differs: {module}")
        check(set(output) == set(re.findall(r"^#print axioms (\S+)$", source.decode(), re.M)),
              f"source and named axiom output disagree: {module}")
        decl_count += len(output)

    return {"scope": manifest.stem, "named_axiom_outputs": decl_count, "fresh_source_rows": len(sources),
            "verified_closure_rows": len(final), "receipt": rid, "omitted_source_logs": omitted_logs}


def main():
    reports = []
    for manifest in sorted(HERE.glob("*.json")):
        try:
            reports.append(package(manifest))
        except (KeyError, ValueError, OSError, RuntimeError) as error:
            print(f"{manifest.name}: {error}", file=sys.stderr)
            return 1
    check(reports, "no Paper 16 manifests found")
    print(json.dumps({"verification": "exact archived source and receipt audit; not a Lean replay",
                      "packages": reports}, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
