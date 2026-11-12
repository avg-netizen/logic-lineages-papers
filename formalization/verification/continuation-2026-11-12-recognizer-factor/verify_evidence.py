#!/usr/bin/env python3
"""Run the unchanged source-matched native verifier for this checkpoint.

This wrapper only selects the checkpoint evidence directory. It neither invokes
Lean nor changes the inherited profile, frozen-source, receipt, object, exact
alias, or axiom checks. Pass --base 4fea270b5f820b4a2b4bb02add9ccb8200bf8e56
with the focused --gate and four --alias arguments after native checks finish.
Candidates remain unaccepted until the native evidence and source review pass.
"""
from pathlib import Path
import importlib.util


HERE = Path(__file__).resolve().parent
SUPPLIER = (HERE.parent / "continuation-2026-11-11" /
            "rank-guarded-representative-complete" / "verify_evidence.py")
SPEC = importlib.util.spec_from_file_location("recognizer_factor_evidence_supplier", SUPPLIER)
VERIFIER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(VERIFIER)
VERIFIER.HERE = HERE


if __name__ == "__main__":
    raise SystemExit(VERIFIER.main())
