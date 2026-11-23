# Paper 16: genuine finite beta paths on the printed native tower terms

Printed source is the actual finite-level (B_l) code in
`ordinals.tex:532–551), the higher-to-lower expression (D) at :563–572,
and the original closed native witnesses (t_n) at :584–591. This is a
rank-free fact about their beta rules, not an interpretation of Fix
or a comparison of the ordinal values of tower terms.

- `NativeTowerBetaBinderProof` proves two literal `Spine.Expr` equations:
  the next outer lambda of the original `bindAscending`, and commuting
  the original `Spine.substitute` through its remaining binders with the
  real depth increment. Its `pending` source has (k) untouched inner
  binders and the already consumed actual value block in nearest-first
  order. The next beta removes the actual outer binder, and
  `BoundBlockProof.block` identifies the closed result with the same
  simultaneous block extended by the actual next right argument.
- `NativeTowerBetaPathProof` takes the closed witness of that literal
  lambda and uses the checked original native beta theorem for its
  real result, Reduction, and confined strict edge. It lifts this step
  through only the original function application slots of all remaining
  right operands, including the untouched final (t_0), with the
  actual `Reduction.context` proof and checked function-slot strictness.
  The root/context beta shape is retained in `FunctionBeta`; arbitrary
  strict edges cannot fill a `BetaStep`.
- The only final source is the genuine `closedTower S (l+2)` from
  #1472, reidentified literally with the original left-associated
  application chain. The (l+1) applications consume
  (B_{l-1},…,B_0,N_B), in that order, into the own extracted (B_l).
  The end is therefore
  `(ordinalFix (λ α. substitute [N_B,B₀,…,B_(l−1)] 1 (inner l))) t0`.
  This exact original Fix and alpha binder remain, and whole terms
  throughout are genuine closed native terms at (o→o).

No externally supplied family, closed intermediate, or edge is used in
the final indexed theorem. “Length (l+1)” means the number of proved
beta/function-context edges in this path, not that no other path or
further reduction exists. No ordinal realization, rank inequality,
cofinality, or numbered promotion.

Named stages: `LogicLineages.PersistentMarking.NativeTowerBetaBinderProof`
(4 reports) and `LogicLineages.PersistentMarking.NativeTowerBetaPathProof`
(3 additional reports). Neither imports ordinal Mathlib.
