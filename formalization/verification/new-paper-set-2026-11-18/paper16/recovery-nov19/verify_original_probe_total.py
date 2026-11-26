"""Replay the two original typed-probe aliases with the previously pinned shared source type."""

import hashlib
import importlib.util
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
TOOLS = ROOT / "verification/local-two-sol-2026-11-18/A"
SHARED = "LogicLineages.OrdinalComparison.SourceTypes"
PAPER = "LogicLineages.PersistentMarking."
NAME = "NumberedWindowOriginalProbeTotalChecks"
PREFIX = "NUMBERED-WINDOW-ORIGINAL-PROBE-TOTAL"


def load(name):
    spec = importlib.util.spec_from_file_location(name, TOOLS / (name + ".py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    receipt = Path(sys.argv[1]).resolve()
    rows = json.loads(receipt.read_text())
    assert rows["requested"] == [PAPER + NAME]
    shared = {r["module"] for r in rows["modules"] if not r["module"].startswith(PAPER)}
    assert shared == {SHARED}, shared
    frozen = HERE / (PREFIX + "-FROZEN.json")
    author = HERE / (PREFIX + "-AUTHOR-MANIFEST.json")
    source = Path(*SHARED.split(".")).with_suffix(".lean")
    shared_freeze = HERE / "NUMBERED-WINDOW-ORIGINAL-COMPUTABILITY-FORMULA-FROZEN.json"
    pins = json.loads(shared_freeze.read_text())["sources"]
    assert pins["formalization/" + str(source)] == hashlib.sha256((ROOT / source).read_bytes()).hexdigest()

    verifier = load("verify_evidence")
    # Both namespaces are under LogicLineages. The explicit allowlist above and
    # the verifier's recursive-closure equality jointly enforce the narrower scope.
    verifier.NAMESPACE = "LogicLineages"
    aliases = [f"PersistentMarking.{NAME}.exact_{clause}" for clause in ("FormulaTypeCoding", "OriginalProbeTotal")]
    report = verifier.verify(receipt, aliases, [frozen, author, shared_freeze])
    evidence = load("acceptance_evidence").export(report)
    destination = HERE / (PREFIX + "-LOCAL-EVIDENCE.json")
    destination.write_text(json.dumps(evidence, indent=2) + "\n")
    print(hashlib.sha256(destination.read_bytes()).hexdigest(), evidence["local_modules"])


if __name__ == "__main__":
    main()
