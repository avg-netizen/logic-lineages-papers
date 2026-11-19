#!/usr/bin/env python3
"""Reconcile a successful cloud core receipt against recovered owner READY packets.

Read-only with respect to the checker, cache, original source and owner evidence.
Outputs new packet-specific acceptance-schema evidence; it does not accept
packets, invoke Lean, or silently treat a partial or failed receipt as a pass.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import shutil

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
PAPER = HERE.parent
OWNER_A = ROOT / "verification/local-two-sol-2026-11-18/A"
PACKETS = {
    "COMPLETENESS": ["ProtectedSpineCompletenessChecks"],
    "SOUND-RELATION": ["ProtectedSpineSoundRelationProof"],
    "SOUND-STAGE": ["ProtectedSpineSoundStageProof"],
    "ADEQUACY": ["ProtectedSpineAdequacyChecks"],
    "DECISION": ["ProtectedSpineDecisionProof"],
    "RPO": ["RankedRestrictionChecks"],
    "NATIVE-CARRIER": ["NativeCarrierChecks"],
}


def load(name):
    spec = importlib.util.spec_from_file_location(name, OWNER_A / f"{name}.py")
    obj = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(obj)
    return obj


owner = load("verify_evidence")
exporter = load("acceptance_evidence")


def cloud_context():
    """Match check.py's --core-profile non-fresh path, without spawning Lean.

    The cloud session uses a direct pinned executable, not the user's Elan
    shim. A different compiler, prefix, path, or imported objects fails the
    independent checked-input-key recomputation in verify().
    """
    checker = owner.checker
    path = shutil.which("lean")
    assert path, "Set PATH to the pinned cloud compiler"
    compiler = Path(path).resolve()
    assert compiler.parent.name == "bin"
    installed = compiler.parent.parent
    assert (installed / "lib/lean/Init.olean").is_file()
    assert installed.name == "lean-4.32.0-rc1-linux", installed
    assert (ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.32.0-rc1"
    packages = ROOT / ".lake/packages"
    if not packages.is_dir():
        packages = checker.CALCULATOR / ".lake/packages"
    search = [checker.BUILD, ROOT, checker.CALCULATOR / ".lake/build/lib/lean"]
    search += [p / ".lake/build/lib/lean" for p in sorted(packages.iterdir()) if p.is_dir()]
    context = {
        "compiler": str(compiler),
        "compiler_sha256": checker.file_digest(compiler),
        "selected_compiler": checker.file_digest(installed / "bin/lean"),
        "lean_path": os.pathsep.join(str(p.resolve()) for p in search),
        "pins": {
            str(base / name): checker.file_digest(base / name)
            for base in (ROOT, checker.CALCULATOR)
            for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml", "lakefile.lean")
        },
    }
    return context, [*map(Path.resolve, search), installed / "lib/lean"]


def reach_closure(results, roots):
    seen = set()

    def visit(module):
        if module not in seen:
            seen.add(module)
            for child in results[module]["local_dependencies"]:
                visit(child.removesuffix(".olean").replace("/", "."))

    for root in roots:
        visit(f"{owner.NAMESPACE}.{root}")
    assert all(m in results for m in seen)
    return seen


def packet_evidence(receipt, packets):
    initial = {packet: json.loads((PAPER / f"LANE-A-{packet}-EVIDENCE.json").read_text())
               for packet in packets}
    aliases = list(dict.fromkeys(a for packet in packets for a in initial[packet]["axioms"]))
    prefix = owner.NAMESPACE + "."
    assert all(a.startswith(prefix) for a in aliases)
    owner.compiler_context = cloud_context
    report = owner.verify(receipt, [a.removeprefix(prefix) for a in aliases], [])
    results = report["recursive_modules"]
    for packet in packets:
        d = initial[packet]
        select = reach_closure(results, PACKETS[packet])
        assert select == {row["module"] for row in d["modules"]}, packet
        for row in d["modules"]:
            assert results[row["module"]]["source_sha256"] == row["source_sha256"], row["module"]
        assert all(report["exact_aliases"][a] == d["axioms"][a] for a in d["axioms"]), packet
        assert all(a.rsplit(".", 1)[0] in select for a in d["axioms"]), packet
        narrowed = {**report, "recursively_verified_union": len(results),
                    "recursive_modules": {m: row for m, row in results.items() if m in select},
                    "exact_aliases": {a: report["exact_aliases"][a] for a in d["axioms"]},
                    "frozen_sources": d["source_pins"]}
        yield packet, exporter.export(narrowed)


def main():
    cli = argparse.ArgumentParser()
    cli.add_argument("receipt", type=Path)
    cli.add_argument("packets", nargs="+", choices=PACKETS)
    args = cli.parse_args()
    outputs = list(packet_evidence(args.receipt.resolve(), args.packets))
    for packet, result in outputs:
        path = HERE / f"LANE-A-{packet}-CLOUD-EVIDENCE.json"
        with path.open("x") as handle:
            handle.write(json.dumps(result, indent=2) + "\n")
        print(exporter.digest(path), path.name,
              f"{result['local_modules']} recursive modules; {result['exact_aliases']} exact audits")


if __name__ == "__main__":
    main()
