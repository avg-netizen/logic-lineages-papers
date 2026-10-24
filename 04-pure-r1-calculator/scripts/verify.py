#!/usr/bin/env python3
"""Check the standalone package and optionally its Lean sources and paper.

Uses installed public dependencies only. Writes VERIFICATION.json. Lean
compilers run serially through check_lean.py; no dependency downloads occur.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
from pathlib import Path
import re
import resource
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))


def lean_modules():
    """All local modules in import order, rejecting missing imports and cycles."""
    sources = {".".join(p.relative_to(ROOT / "lean").with_suffix("").parts): p
               for p in (ROOT / "lean").rglob("*.lean") if ".lake" not in p.parts}
    ordered, active, done = [], set(), set()

    def visit(name):
        if name in active:
            raise RuntimeError(f"Cyclic local Lean imports at {name}")
        if name in done:
            return
        if name not in sources:
            raise RuntimeError(f"Missing local Lean import {name}")
        active.add(name)
        source = re.sub(r"/-.*?-/|--[^\n]*", "", sources[name].read_text(), flags=re.S)
        for line in source.splitlines():
            match = re.match(r"\s*import\s+(.+)", line)
            if match:
                for dependency in match.group(1).split():
                    if dependency == "R1Calculator" or dependency.startswith("R1Calculator."):
                        visit(dependency)
                    elif dependency != "Mathlib" and not dependency.startswith(("Mathlib.", "Lean.")):
                        raise RuntimeError(f"Undocumented external Lean dependency {dependency}")
        active.remove(name)
        done.add(name)
        ordered.append(sources[name].relative_to(ROOT / "lean").as_posix())

    for name in sorted(sources):
        visit(name)
    return ordered


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", action="store_true")
    parser.add_argument("--paper", action="store_true")
    args = parser.parse_args()
    steps = []

    def run(command, timeout=60):
        start = time.monotonic()
        result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=timeout, check=False)
        output = result.stdout
        print(output, end="" if output.endswith("\n") else "\n", flush=True)
        display = ["python3" if index == 0 and word == sys.executable else word
                   for index, word in enumerate(command)]
        steps.append({"command": display, "returncode": result.returncode,
                      "elapsed_seconds": round(time.monotonic() - start, 3)})
        if result.returncode:
            raise RuntimeError(f"Check failed: {' '.join(display)}")
        return output

    tests = run([sys.executable, "-m", "unittest", "discover", "-s", "tests", "-v"])
    match = re.search(r"Ran (\d+) tests", tests)
    if not match:
        raise RuntimeError("No completed Python test-suite receipt")
    run([sys.executable, "scripts/generate_examples.py", "--check"])
    from r1calc import endpoint, parse_ordinal
    fixtures = json.loads((ROOT / "examples/endpoint-fixtures.json").read_text())
    for case in fixtures["cases"]:
        if endpoint(parse_ordinal(case["input"])) != parse_ordinal(case["endpoint"]):
            raise RuntimeError(f"Python disagrees with explicit fixture: {case}")

    allowed_axioms = {"propext", "Classical.choice", "Quot.sound"}
    axiom_checks = {}
    modules = []
    if args.lean:
        modules = lean_modules()
        for relative in modules:
            source = (ROOT / "lean" / relative).read_text()
            without_comments = re.sub(r"/-.*?-/|--[^\n]*", "", source, flags=re.S)
            if re.search(r"\b(?:sorry|admit|axiom|native_decide|ofReduceBool)\b", without_comments):
                raise RuntimeError(f"Unproved declaration in {relative}")
        output = run([sys.executable, "scripts/check_lean.py", *modules],
                     timeout=max(390, len(modules) * 95))
        for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output):
            dependencies = {part.strip() for part in axioms.split(",") if part.strip()}
            if not dependencies <= allowed_axioms:
                raise RuntimeError(f"Unexpected axioms in {name}: {dependencies}")
            axiom_checks[name] = sorted(dependencies)
        if len(axiom_checks) < 10:
            raise RuntimeError("Expected principal theorem axiom reports are missing")
        required = {"R1Calculator.PureR1.endpoint_semantic",
                    "R1Calculator.PureR1.intervalCheck_iff_sigma1",
                    "R1Calculator.PureR1.endpoint_isGreatest",
                    "R1Calculator.endpoint_treeWeight_bound",
                    "R1Calculator.endpoint_treeWeight_bound_sharp"}
        if not required <= axiom_checks.keys():
            raise RuntimeError(f"Missing core theorem reports: {required - axiom_checks.keys()}")

    pdf = None
    if args.paper:
        run([sys.executable, "build_pdf.py"], timeout=90)
        fonts = run(["pdffonts", "paper.pdf"])
        font_names = []
        for line in fonts.splitlines()[2:]:
            if not line.strip():
                continue
            name = line.split()[0].split("+")[-1]
            if not name.startswith("CM") or not re.search(
                    r"\s+yes\s+(?:yes|no)\s+(?:yes|no)\s+\d+\s+\d+\s*$", line):
                raise RuntimeError(f"Unexpected or non-embedded paper font: {line}")
            font_names.append(name)
        log = (ROOT / "paper.log").read_text(errors="replace")
        if re.search(r"Overfull \\[hv]box|Missing character|(?:Citation|Reference) .+ undefined", log):
            raise RuntimeError("PDF has a layout, glyph, citation or reference defect")
        info = run(["pdfinfo", "paper.pdf"])
        page_count = re.search(r"^Pages:\s+(\d+)", info, re.M)
        pdf = {"pages": int(page_count.group(1)), "fonts": sorted(set(font_names)),
               "sha256": hashlib.sha256((ROOT / "paper.pdf").read_bytes()).hexdigest()}

    sources = sorted([*ROOT.glob("r1calc/*.py"), *ROOT.glob("tests/*.py"),
                      *ROOT.glob("scripts/*.py"), *ROOT.glob("lean/**/*.lean"),
                      ROOT / "paper.tex", ROOT / "preamble.tex", ROOT / "pyproject.toml",
                      ROOT / "lean/lakefile.toml", ROOT / "lean/lake-manifest.json",
                      ROOT / "lean/lean-toolchain", ROOT / "examples/endpoint-fixtures.json"])
    source_hashes = {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                     for p in sources if ".lake" not in p.parts}
    record = {
        "checked_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "status": "PASS", "python_tests": int(match.group(1)),
        "explicit_endpoint_fixtures": len(fixtures["cases"]),
        "lean_checked": args.lean, "lean_modules": modules,
        "lean_axiom_dependencies": axiom_checks,
        "paper_checked": args.paper, "paper": pdf,
        "maximum_child_rss_kib_linux": resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
        "steps": steps, "source_sha256": source_hashes,
        "scope": "Python execution tests; Lean arithmetic, finite-pattern, standalone recursive "
                 "Sigma1 semantics, finite-copy/obstruction proofs, full semantic endpoint rows "
                 "for normal left inputs and arbitrary right ordinals, and sharp expanded-tree "
                 "norm bounds; PDF assembly. No external Carlson correctness premise. "
                 "Standard Lean/Mathlib foundations remain dependencies. No Python refinement, "
                 "higher-order/additive relation evaluator, independent human review or priority claim."
    }
    (ROOT / "VERIFICATION.json").write_text(json.dumps(record, indent=2) + "\n")
    print("Verification PASS; wrote VERIFICATION.json")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
