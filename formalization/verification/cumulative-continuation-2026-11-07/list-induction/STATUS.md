# Checked internal list induction — 7 November 2026

Eleven new exact supporting targets pass in the focused module
`LogicLineages.ExternalCheckpoint20261107ListInduction`:

| Component | Exact targets | Result |
|---|---:|---|
| Full-language strong induction | 3 | Original-calculus schema, contextual rule and symbolic-term instance |
| Original list-code induction | 2 | First-order nil/cons schema and contextual use at any code |
| Original natural-list parser | 6 | Totality, unique decoding, encoding bijection, decoding equation, size bounds and exact fuel criterion |

The list theorem covers every natural code. Its invariant can contain the
inductive predicate with arbitrary polarity and can retain arbitrary free
parameters and ambient hypotheses. The constructor premise uses the unchanged
original `consCode` graph. Internal program totality, reconstruction and strict
tail descent provide the witnesses and decreasing argument.

The parser theorem uses the unchanged `numbersParse`, `decodeNumbers` and
`numbersNumber`. Its exact success criterion is
`numbersParse fuel value = some xs` iff
`numbersNumber xs = value` and `xs.length < fuel`. Every natural has exactly
one decoded natural list; this does not assert validity as a typed term or
certificate.

## Verification

The focused aggregate passed under the pinned Lean `v4.32.0-rc1` toolchain and
Mathlib commit `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`.
Its **1,039 local source modules** match successful native receipts. All
**11 exact aliases** pass the standard-axiom audits. Strong induction uses
only `propext` and `Quot.sound`; list induction and parser totality additionally
use `Classical.choice` through their existing suppliers.

The unchanged serialized profile used one worker, a 2,048 MiB heap cap,
1,536 MiB RSS cap, 2,048 MiB free-memory floor, 90-second CPU limit and
180-second wall limit per compiler invocation. Peak successful observed
process-tree RSS was **1,232,216 KiB**. No full public-root build or remote CI
result is claimed.

The proof repairs were limited to namespace qualification, an explicitly
typed three-term substitution tuple, an explicit list-entry substitution,
and locating each namespace audit in its own statement-check module. All
five frozen new definition/target files are unchanged. Existing proof and
definition files are unchanged; the public root imports the new checkpoint.

See [ACCEPTANCE.json](ACCEPTANCE.json), [frozen targets](FROZEN-TARGETS.json),
[source correspondence](SOURCE-CORRESPONDENCE.md), and the accepted
[strong-induction](strong-induction.log), [list-induction](list-induction.log)
and [parser](parser-totality.log) audit logs.

## Remaining work

These are supporting results for paper 06 `lem:id1`. The original
source-specific multiset, constructor, lambda, computable-substitution and
all-term accessibility derivations remain unfinished. The numbered statement
register remains **168 checked, 2 inherited and 19 pending out of 189**.
The next consumer is internal reasoning over the original finite-list and
certificate graphs using the new full-language list-induction rule.
