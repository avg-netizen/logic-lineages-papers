# Independent statement review, 20–21 November 2026

Reviewer: a fresh-context Claude subagent (same model family as the author; no access to the author's
reasoning), read-only, no compiler, no Git writes. **This is weaker independence than the cross-model review
used for accepted records 615–698**, and is recorded as such. Compilation and axiom closure were not
re-checked by the reviewer; they are covered by the native gate and the recursive evidence file.

Scope: the fourteen frozen statements in the five `NumberedWindowInternalSparseRaw…Targets.lean` files
(`TickShape`, `RunShape`, `RunSuccess`, `RunLift`, `RunRoot`), their `exact_…` theorems, the plan documents,
and the unchanged definitions they are about.

## Round 1 — twelve statements (tick shape, run shape, success, lift): PASS WITH NOTES

- All twelve FAITHFUL. Each `exact_X` has type exactly `ExactX`; no `variable` in any checks file.
- `goodState`: outer binder is the flag (`.inl (.inr 0)`), inner the frame (`.inr 0`), `out` relabelled
  twice and not captured; same convention as `hasPreimage` and `witnessesIntro`. Not trivially true
  (`out = 0` and `stateTerm 1 1` are not good).
- Premises satisfiable; `start` and the reached terminal output are distinct terms in the extra-fuel and
  lift statements; the tick input is pack-shaped with free flag and frame; `ltF fuel more` means
  `fuel < more`.
- The three declared deviations (successor flag, `ltF` premise, arbitrary ternary tape) are at least as
  strong as the plan. `numeral 1` is definitionally `suc z`.
- `ExactOpenLiftedOwnRun`: slot order identical to `ExactOpenLiftedTick`; true on the standard naturals for
  every callback (first parent tick is callback-independent, the wrapper code minus one is at least the
  child, a successor-flag state has frame zero and is a tick fixed point); premise satisfiable.
- No tracked file modified; no forbidden token in the new files.
- N1 (applied): the remark that the successor step does not use `goodState start` describes the derivation
  only; the premise is not redundant at positive fuel.
- N2 (not applied, Targets frozen): the doc comment of `ExactOpenRawRunLift` says "on its own fuel" although
  `fuel` is arbitrary there. The statement is more general than its comment.
- N3: the reviewer did not verify the register count, the receipt or the evidence file.

## Round 2 — root statements: PASS

- `rootWitnessTerm`, `ExactOpenRootTick`, `ExactOpenRootOwnRun` FAITHFUL.
- `rootWitnessTerm payload` is `packNode 0 [payload]` by reading the definitions; `rootReports` and
  `tagFiveZero` give the object-level test results. **No theorem here states the numeric identification
  with `unpackNode`.**
- `ExactOpenRootOwnRun` is true in both directions for every `Program 3` and valuation; fixing the flag at
  `suc z` is necessary (with `suc k` the equivalence would be false for a root output of two).
- Not established: the original `raw` relation (it also needs the `syntaxBits` conjuncts), that `p` is an
  `ActualRoot`, the fallback branches, typed or least semantics, `RawMatching`, ID1 membership, the
  Bachmann–Howard bound, any promotion.
