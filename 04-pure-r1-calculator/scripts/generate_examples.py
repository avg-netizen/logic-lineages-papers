#!/usr/bin/env python3
"""Generate Lean computations from explicit, independently stated fixtures.

Only parsing and notation serialization use Python here. Expected endpoint
values come from the fixture file, never from the Python endpoint routine.
"""
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from r1calc import lean_term, parse_ordinal  # noqa: E402


def rendered() -> str:
    fixture = json.loads((ROOT / "examples/endpoint-fixtures.json").read_text())
    if fixture["schema"] != "r1calc.endpoint-fixtures.v1":
        raise ValueError("Unsupported fixture version")
    lines = [
        "import R1Calculator.Ordinal", "import R1Calculator.Patterns", "",
        "/- Generated from examples/endpoint-fixtures.json by scripts/generate_examples.py.",
        "Expected endpoints are explicit fixtures, not outputs of Python endpoint. -/",
        "namespace R1Calculator.Examples", "",
    ]
    for index, case in enumerate(fixture["cases"]):
        source = lean_term(parse_ordinal(case["input"]))
        expected = lean_term(parse_ordinal(case["endpoint"]))
        lines += [f"theorem endpoint_fixture_{index} :",
                  f"    endpoint {source} = {expected} := by decide", ""]
    lines += [
        "example : coversCheck (discrete 2) (chain 2) = true := by decide",
        "example : embedsCheck (discrete 2) (chain 2) = false := by decide",
        "example : markedCoversCheck (discrete 2) (discrete 2) = false := by decide",
        "", "end R1Calculator.Examples", "",
    ]
    return "\n".join(lines)


if __name__ == "__main__":
    target = ROOT / "lean/R1Calculator/Examples.lean"
    output = rendered()
    if "--check" in sys.argv:
        if not target.exists() or target.read_text() != output:
            raise SystemExit("Lean example source is stale; regenerate it.")
        print("Lean examples match the explicit fixture file.")
    else:
        target.write_text(output)
        print("Generated lean/R1Calculator/Examples.lean")
