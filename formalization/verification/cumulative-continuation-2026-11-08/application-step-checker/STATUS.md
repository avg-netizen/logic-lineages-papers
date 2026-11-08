# Normalized original application-step checker: exact gate passed

Two supporting targets are checked at their unchanged frozen types:

1. The concrete normalized checker equals the original `numericStepTest`
   on every natural input triple, assuming separate all-input calibrations
   of its endpoint leaf and old checker.
2. In the original internal calculus, the same normalized checker has
   equivalent full-output graphs on original and lifted source, target and
   certificate terms. Actual original tag, leaf and constructor graphs
   remain explicit premises.

Both exact comparator aliases and both public theorem axiom closures passed
using only `propext`, `Classical.choice` and `Quot.sound`. All 1,094 local
modules in the focused import closure have matching successful native source
receipts. The three frozen specifications and 31 original prerequisite pins
are unchanged. The original serialized resource profile was retained.

This supplies neither the concrete endpoint leaf nor the original internal
typed-guard derivations, representative congruence, invariant propagation,
joint-context and outer `pathValue` assembly, CertifiedApplicationLift, or
full paper06 ID1. No numbered source statement is promoted. No full-root,
remote-CI or Git action is claimed.

The portable checkpoint is seven accepted Lean files plus the five evidence
files listed in `SOURCE-CORRESPONDENCE.md`. Raw receipts, logs and all proof
candidates remain local. See `ACCEPTANCE.json` for the exact validation scope.

Reproduction module:
`LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepCheckerStatementChecks`.

Use the unchanged serialized resource profile:

    python3 scripts/check.py --memory-mib 2048 --rss-mib 1536 --min-free-mib 2048 --threads 1 --cpu-seconds 90 --timeout 180 LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepCheckerStatementChecks
