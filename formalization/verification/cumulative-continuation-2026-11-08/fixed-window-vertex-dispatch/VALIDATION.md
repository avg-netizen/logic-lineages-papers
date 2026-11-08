# Validation: fixed-window vertex dispatch

## Exact statement gate

The three amended specification files were independently accepted and passed
comparator-only native preflight before proof authoring. `AMENDMENT-01.json`
records the sole changes to the initial freeze: use of the expanded internal
equality constructor and two explicit graph namespace qualifications. No
mathematical contract changed. All amended frozen files and their 65 source
and prerequisite pins remain unchanged through the successful exact gate.
Historical freeze/static records are retained as such; this validation records
the later checked state.

All five aliases in `InternalFixedWindowVertexDispatchStatementChecks.lean`
have the exact frozen Preflight comparator types and explicit actual-axiom
checks. Their dependencies are only `propext`, `Classical.choice`, and
`Quot.sound`. All 31 namespace audit entries, including those five aliases,
pass the same permitted-foundation audit. There are no added axioms,
placeholder proofs, native decision shortcuts, or semantic truth-to-internal-
derivation rules in the accepted sources.

## Source-matched focused closure

The collector follows local source imports, including meta imports, from
StatementChecks and Preflight. Each of the 1,222 current local module
hashes matches a successful row in an immutable numeric build receipt, with
its log and receipt hashes verified. There are 60 distinct immutable receipts.
Successful supplier rows are reused; this is not a fresh whole-closure or
full-root build. Mutable latest aliases and symlink receipts are excluded.
`SOURCE-PINS.json` contains the exact local source closure.

- Closure pins SHA256: `78aa313755a712250b61180656b79c4da1e14b57b347bd7259831379b4e18bc6`.
- Comparator-preflight receipt SHA256: `9e5757922e946e352764fc3ebb366956a1e07558fc136f73a719277078429446`.
- Final successful exact-check receipt SHA256: `f87c6a6922e08fecb7bb001a71207949455d66a10aeb37c75edd468b6c88658f`.
- Peak observed successful closure RSS: 1,176,760 KiB.
- Peak observed component RSS: 1,096,396 KiB.

The unchanged serialized profile uses one thread, 2,048 MiB Lean heap,
1,536 MiB process-tree RSS, a 2,048 MiB minimum free-memory floor, 90 CPU
seconds and 180 wall seconds per module. Only pinned upstream cache objects
are used. No compiler resource limit was raised to repair proofs.

Portable reproduction command, run from `formalization` with the pinned
toolchain and already available pinned dependency cache:

`python3 scripts/check.py --memory-mib 2048 --rss-mib 1536 --min-free-mib 2048 --threads 1 --cpu-seconds 90 --timeout 180 LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchStatementChecks`

## Repair and retention

The first internal support check passed. Two evaluation-proof candidates
required only elaboration repairs: avoiding already-closed tactic goals,
explicit natural-vector normalization, a local decidability instance and its
current syntax. The external mathematical equality and all frozen targets
remained unchanged. The successful exact check contains no errors or
placeholder dependencies. Earlier failed candidates, raw logs, complete
immutable receipts and the source-to-receipt map remain local and are excluded
from the portable packet.

## Scope

The proof recovers original canonical typed children through the checked
selected typed calibration. The existing total type decoder supplies exact
type-number equations for every natural coordinate. The checked original
`typedApplicationCombine`, canonical-application calibration and fixed-context
decoded-application calibration identify the same original result. The
inactive branch keeps the original vertex on every other input.

The internal proofs use literal constant-AST induction, equality acceptance,
exact-one conjunction, original graph composition and conditional branch
rules. They conclude the actual C graph, not canonicality of its output.
The generic path API and optional invariant are not claimed by this packet.
No numbered source status, Git publication, full-root build or remote CI
result is asserted. Final independent coordinator checkpoint review remains
pending.
