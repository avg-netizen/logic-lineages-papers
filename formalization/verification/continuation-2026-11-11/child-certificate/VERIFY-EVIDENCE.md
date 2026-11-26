# Native evidence verifier

Run from `formalization` with one or more `--gate MODULE` and optional repeated
`--alias FULL_DECLARATION_NAME` arguments:

```
python verification/continuation-2026-11-11/child-certificate/verify_evidence.py \
  --gate LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalQuotientSpineStatementChecks \
  --alias FULL_EXACT_ALIAS_NAME
```

Use the actual aliases declared by each gate. Do not substitute a guessed alias.
The program does not run Lean or modify mathematical/checker sources. Each run
creates a fresh timestamped subdirectory of this checkpoint's `runs` directory.
It exits 0 only when the selected local closure has current successful native
rows, unchanged fixed resource settings, all expected native object outputs,
non-stale objects, matching frozen specifications, unchanged inherited files
(except the explicit mutable allowlist), and any requested exact-alias axiom
prints. Source placeholders and added axioms are rejected like the checker.

The report is `native-evidence-verified` or `pending`. Neither status claims
manuscript correspondence, mathematical adoption, a root build or remote CI.
Only the coordinator may accept the exact source target after reviewing that
correspondence. Dependency binary-cache provenance is separate: this verifier
records direct external imports but does not independently repeat the official
upstream-cache restoration audit.

Every readable attempt receipt and native log is preserved in compressed JSON,
including failures. Run after native jobs and source editing stop for a stable
final snapshot. A snapshot during an active build may be incomplete and reports
unreadable or changing input as pending. Original `build-reports` are untouched.

Smoke validation: the already-passed quotient preflight closure (1,215 modules)
produced two zero-error snapshots while candidate proofs were still pending.
Python syntax compilation also passed. These checks do not claim any new Lean
proof result.
