# Source introduction checkpoint — 5 November 2026

**Accepted: five exact supporting targets in two gates.** Every original
`SourceFormula` now has a concrete quantified occurrence-row translation with
equivalent evaluation under every original valuation, exact free-variable
membership and a literal primitive-recursive numeric compiler.

Together with the [eleven term-graph targets](../source-term-graph/STATUS.md),
this continuation adds **sixteen targets in four gates**. The cumulative branch
`formalization/cumulative-continuation-2026-11-04` contains **24 checked targets
in six gates**, including the eight normal-form targets accepted at `eb0dd98`.

Original negation, conjunction and named existential binders remain in place.
Each source atom receives its own local witness block. The allocator includes
all original names occurring in that atom, including those bound by enclosing
source quantifiers. Equality compares the two child graph outputs; strict
order uses the exact row `y - x - 1 >= 0`. Original names are never renamed,
and ordinary binder shadowing is preserved.

The numeric compiler follows the original radix-5 source encoding and returns
the exact encoded typed translation. Its full graph generation, fresh-name
calculation, comparison and witness binding are primitive recursive. Proof-only
repairs addressed list association, explicit theorem specialization and typed
numeric composition. All frozen definitions and comparison types are unchanged;
compiler and heartbeat limits were not increased.

The final aggregate `LogicLineages.ExternalCheckpoint20261105SourceIntroduction`
passed in [receipt 1793838387406023253-2](../source-term-graph/receipts/1793838387406023253-2.json).
All **133 local modules** have successful receipts matching their current
hashes, and all sixteen new exact aliases have standard-axiom audits. The
[acceptance record](ACCEPTANCE.json) links the complete
[source closure](../source-term-graph/SOURCE-CLOSURE.json) and
[raw compiler logs](../source-term-graph/COMPILER-LOGS.json).

The source register remains **161 checked, 2 inherited and 26 pending / 189**.
This intermediate language retains quantified blocks inside source negations.
The full `EffectiveSourceExistentialNormalForm`, `EffectiveExpandedElimination`
and `FullSourceDecision` propositions remain pending. The next mathematical
stage must eliminate negated witness blocks with the required normal-form
closure and decreasing induction; this checkpoint does not replace that work.
No full public-root build or remote-CI pass is claimed.

Read [SOURCE-CORRESPONDENCE.md](SOURCE-CORRESPONDENCE.md) for the exact source
boundary and [FROZEN-TARGETS.json](FROZEN-TARGETS.json) for the pre-authoring pins.
