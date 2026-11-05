# Cumulative continuation: normal-form semantics and compiler

Result: all eight supporting targets and the focused 110-module closure are
checked. Read the [accepted checkpoint](verification/cumulative-continuation-2026-11-04/normal-form/STATUS.md)
and [exact acceptance evidence](verification/cumulative-continuation-2026-11-04/normal-form/ACCEPTANCE.json).

The user explicitly requested continuation of the public formalization and
authorized a cumulative branch for commits on 4 November 2026. This release
supersedes the completed six-lane pause for the work recorded here. The
historical pause receipts, draft archive and accepted source files remain
evidence of their original checkpoints.

The starting point is merged `main` at
`ba2dec0` (the reconciliation checkpoint from pull request 8). Every remote
continuation branch was already an ancestor of this base. The current branch
is `formalization/cumulative-continuation-2026-11-04`.

## Exact continuation target

Complete the eight supporting propositions in
`SnyatkovCompletion/NormalFormTargets.lean`: original domain cutoffs, signed
row decomposition, all-occurrence domain guards, atom and Boolean compilation,
exact variable membership, literal code calibration, and actual numeric
programs. These continue the specific unproved normal-form targets preserved
by the Snyatkov lane at the preceding pause.

The definitions and targets were restored byte for byte from the preserved
draft archive. Their SHA-256 values match the successful historical
target-only preflight in
`verification/local-resume-2026-11-04-six-lanes/sol3-snyatkov/NORMAL-FORM-TARGET-ONLY-FROZEN.json`:

| File | SHA-256 |
|---|---|
| `NormalFormDefinitions.lean` | `cd3538ab8a53a5ba61572775d8fb22572b2870fc460a99a9f0027c866868c148` |
| `NormalFormTargets.lean` | `15a399fbcc1c6a08ef771d61243cf73d44be88b92e2ac6396c8ed202bf6eaead` |

Semantic proofs and compiler proofs have separate file ownership. Native
checks are serialized through `scripts/check.py`, with the existing one-worker
2048 MiB heap, 1536 MiB RSS, 2048 MiB available-memory admission, 90-second CPU
and 180-second per-module wall limits. The pinned Lean and Mathlib versions
are unchanged; upstream objects are acquired from the official cache.

## Source boundary

The target retains all original summand occurrences, including zero and
cancelled coefficients; signed-domain guards remain at their actual Boolean
positions. The hyperfunction cutoff retains the explicit below-range
`H(0) = 1` case. The numeric program is a total all-code compiler, and source
calibration concerns actual encoded syntax.

The full source existential normal form, closure under all elimination
branches, the decreasing quantified-block induction and full arbitrary
first-order BASE decision remain distinct pending targets. No numbered source
statement is promoted by proving these eight supporting propositions. The
starting register is 161 checked, 2 inherited and 26 pending out of 189.

Acceptance requires exact statement gates, actual transitive axiom audits
limited to `propext`, `Classical.choice` and `Quot.sound`, and recorded source
hashes. Historical author sessions and unrelated work are not restarted by
this bounded continuation. Publication is to the cumulative branch; no main
merge or CI configuration change is part of this checkpoint.
