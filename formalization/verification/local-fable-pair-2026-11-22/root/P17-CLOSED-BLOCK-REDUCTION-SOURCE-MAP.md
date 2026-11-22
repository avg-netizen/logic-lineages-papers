# Paper 17: `thm:arithmetic` reduced to one emission statement

Paper statement (`17-permitted-control-canonical-comparison/sections/arithmetic.tex`, `thm:arithmetic`):
for either control, closed existential and closed universal Boolean combinations of linear
inequalities, equalities and congruences over finite circuits of fixed-head collapses are decidable.

Frozen target `LogicLineages/PermittedControl/ClosedBlockDecisionTargets.lean`
(sha256 `56edf93074550b19ad73ed0c4002dd845aa95a8043340d2570e65989c82c1fb0`):

- `Decides f decide` — literally the three clauses of accepted #1372 `ForControl` (existential query,
  its negation, universal query through the opposite polarity) on every encoded topological circuit
  and plain prepared matrix, with the callback-free `decide` in place of `result f B high`.
- `DecidableClosedBlocks f` — `∃ decide, Computable decide ∧ Decides f decide`.
- `ClosedBlockDecision` — that for `factorialControl` and every `nearControl b`. **Proposed comparator
  for `thm:arithmetic`; not proved, not promoted.** Its correspondence to the printed statement rests on
  #1372's own source scope (what `HasSuccessfulObservation` / `EverySuccessfulObservation`, `encodeInput`,
  `Topological` and `PlainPreparedFormula` cover); root authored it and nobody has reviewed that
  correspondence. Points a reviewer should look at: fixed heads "arbitrary below ε₀" versus the gate
  language of `Gate`; "preserves shared inputs and shared circuit nodes" is carried by the circuit
  encoding, not stated separately; the answer type is `Option Bool` and is `none` exactly on non-codes
  (#1372 `ExactOriginalRawStageFailure`).
- `ComputableEmitter f B` — some shaped, exact supplier (#1387 interface) and a computable raw `high`
  with the literal emission equation `Emits`.
- `ExactClosedBlockFromEmitter`, `ExactClosedBlockReduction` — proved: a computable emitter at the
  factorial control (threshold 0) and at each near control (threshold b+1) gives `ClosedBlockDecision`.

Proof: #1387 `fixed_exactSuppliedStageCallback` turns the emitter into `HighAtStage`; #1372
`fixed_exactOriginalRawSelectedStageQuery` then gives the three clauses and computability of
`result f B high`.

What remains for `thm:arithmetic`, exactly: `ComputableEmitter factorialControl 0` and
`∀ b, ComputableEmitter (nearControl b) (b + 1)`. With #1395 the supplier half is available for the
canonical supplier (or a level-order variant with the same members); the open half is the raw program.
