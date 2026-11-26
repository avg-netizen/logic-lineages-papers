#!/usr/bin/env python3
"""Reconcile a completed paper16 gate with the recursive native cache, read-only."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PAPER = ROOT / "verification/new-paper-set-2026-11-18/paper16"
NAMESPACE = "LogicLineages.PersistentMarking"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
CORE_PROFILE = {
    "heap_cap_mib": 1536, "rss_cap_mib": 512, "wall_seconds": 180, "cpu_seconds": 90,
    "minimum_free_mib": 768, "core_only_profile": True, "single_thread": True,
    "threads": 1, "upstream_cache_only": True,
}
spec = importlib.util.spec_from_file_location("native_checker", ROOT / "scripts/check.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


def compiler_context():
    """Rebuild the local core cache context without launching a compiler."""
    compiler = Path(shutil.which("lean")).resolve()
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    elan = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan"))
    installed = elan / "toolchains" / toolchain.replace("/", "--").replace(":", "---")
    packages = ROOT / ".lake/packages"
    if not packages.is_dir():
        packages = checker.CALCULATOR / ".lake/packages"
    search = [checker.BUILD, ROOT, checker.CALCULATOR / ".lake/build/lib/lean"]
    search += [p / ".lake/build/lib/lean" for p in sorted(packages.iterdir()) if p.is_dir()]
    return {
        "compiler": str(compiler),
        "compiler_sha256": checker.file_digest(compiler),
        "selected_compiler": checker.file_digest(installed / "bin/lean"),
        "lean_path": os.pathsep.join(str(p.resolve()) for p in search),
        "pins": {
            str(base / name): checker.file_digest(base / name)
            for base in (ROOT, checker.CALCULATOR)
            for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml", "lakefile.lean")
        },
    }, [*search, installed / "lib/lean"]


def frozen_pins(manifest):
    pins = json.loads(manifest.read_text())["sources"]
    for path, digest in pins.items():
        assert checker.file_digest(ROOT.parent / path) == digest, f"Frozen source changed: {path}"
    return pins


def imports(source):
    code = source.read_text()
    for block in re.findall(r"/-.*?-/", code, re.S):
        assert not checker.IMPORT.search(block), f"Import inside comment requires review: {source}"
    return [name for line in checker.IMPORT.findall(code) for name in line.split()]


def verify(receipt_path, aliases, manifests):
    receipt = json.loads(receipt_path.read_text())
    assert "outcome" not in receipt, receipt.get("outcome")
    assert all(receipt[k] == v for k, v in CORE_PROFILE.items()), "Core profile mismatch"
    checked = {row["module"]: row for row in receipt["modules"]}
    base_context, search = compiler_context()
    assert base_context["selected_compiler"], "Pinned local compiler not found"
    results = {}
    axioms = {}

    def visit(module):
        if module in results:
            return
        source = checker.source_for(module)
        assert source, f"Missing source: {module}"
        assert module.startswith(NAMESPACE + "."), f"Unexpected local dependency: {module}"
        dependencies = []
        external_objects = {}
        for dependency in imports(source):
            relative = Path(dependency.replace(".", "/") + ".olean")
            if checker.source_for(dependency):
                visit(dependency)
                dependencies.append(checker.BUILD / relative)
            else:
                assert dependency.startswith(("Init", "Lean", "Std")), dependency
                external = next((path / relative for path in search if (path / relative).is_file()), None)
                assert external, f"Missing external object: {dependency}"
                external_objects[dependency] = checker.object_bundle(external)
        target = checker.BUILD / (module.replace(".", "/") + ".olean")
        context = {**base_context, "external_objects": external_objects}
        key = checker.checked_input_key(source, dependencies, context)
        row = checker.checked_cache_hit(target, key, CORE_PROFILE)
        assert row is not None, f"Source/object/profile/receipt mismatch: {module}"
        expected = checked[module]
        assert expected["returncode"] == 0 and expected["log"] == row["log"], module
        assert row["source_sha256"] == checker.file_digest(source), module
        log = ROOT / row["log"]
        log_text = log.read_text()
        for name, axiom_text in re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]", log_text, re.M):
            found = [item.strip() for item in axiom_text.split(",") if item.strip()]
            assert set(found) <= STANDARD_AXIOMS, f"Unexpected axioms in {name}: {found}"
            axioms[name] = found
        for name in re.findall(r"^'([^']+)' does not depend on any axioms", log_text, re.M):
            axioms[name] = []
        native_receipt = Path(row["verified_from"])
        results[module] = {
            "source_sha256": row["source_sha256"],
            "input_key": key,
            "local_dependencies": [str(path.relative_to(checker.BUILD)) for path in dependencies],
            "external_objects": external_objects,
            "objects": {str(Path(path).relative_to(ROOT)): value
                        for path, value in checker.object_bundle(target).items()},
            "native_receipt": str(native_receipt.relative_to(ROOT)),
            "log": row["log"],
            "log_sha256": checker.file_digest(log),
            "peak_rss_kib": row["peak_process_tree_rss_kib"],
        }

    for module in receipt["requested"]:
        visit(module)
    assert results.keys() == checked.keys(), "Receipt import closure differs from current source"
    required = [f"{NAMESPACE}.{alias}" for alias in aliases]
    assert set(required) <= axioms.keys(), f"Missing axiom audits: {set(required) - axioms.keys()}"
    pins = {}
    for manifest in manifests:
        pins.update(frozen_pins(manifest))
    return {
        "status": "source-matched",
        "gate": str(receipt_path.relative_to(ROOT)),
        "gate_sha256": checker.file_digest(receipt_path),
        "profile": CORE_PROFILE,
        "compiler": base_context,
        "frozen_sources": pins,
        "exact_aliases": {name: axioms[name] for name in required},
        "recursive_modules": results,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("receipt", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("aliases", nargs="+")
    parser.add_argument("--manifest", type=Path, action="append", default=[])
    args = parser.parse_args()
    report = verify(args.receipt.resolve(), args.aliases,
                    [PAPER / "MARKED-CONSTRUCTOR-FROZEN.json", *args.manifest])
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Verified {len(report['recursive_modules'])} modules, {len(args.aliases)} exact aliases, "
          f"and {len(report['frozen_sources'])} frozen hashes.")


if __name__ == "__main__":
    main()
