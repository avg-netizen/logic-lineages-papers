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
    if args.lean:
        modules = ["R1Calculator/Ordinal.lean", "R1Calculator/Patterns.lean",
                   "R1Calculator/Examples.lean", "R1Calculator.lean"]
        for relative in modules:
            source = (ROOT / "lean" / relative).read_text()
            without_comments = re.sub(r"/-.*?-/|--[^\n]*", "", source, flags=re.S)
            if re.search(r"\b(?:sorry|admit|axiom)\b", without_comments):
                raise RuntimeError(f"Unproved declaration in {relative}")
        output = run([sys.executable, "scripts/check_lean.py", *modules], timeout=390)
        for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output):
            dependencies = {part.strip() for part in axioms.split(",") if part.strip()}
            if not dependencies <= allowed_axioms:
                raise RuntimeError(f"Unexpected axioms in {name}: {dependencies}")
            axiom_checks[name] = sorted(dependencies)
        if len(axiom_checks) < 10:
            raise RuntimeError("Expected principal theorem axiom reports are missing")

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
        "lean_checked": args.lean, "lean_axiom_dependencies": axiom_checks,
        "paper_checked": args.paper, "paper": pdf,
        "maximum_child_rss_kib_linux": resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
        "steps": steps, "source_sha256": source_hashes,
        "scope": "Python execution tests; named Lean arithmetic/finite-pattern proofs; PDF assembly. "
                 "Carlson semantic identification is cited externally. No Python refinement, "
                 "new semantic theorem, independent mathematical review or priority claim."
    }
    (ROOT / "VERIFICATION.json").write_text(json.dumps(record, indent=2) + "\n")
    print("Verification PASS; wrote VERIFICATION.json")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
