module
public import LogicLineages.OrdinalComparison.ActualNormBalls

@[expose] public section

/-! The literal finite maximum on actual source ordinals.

Paper 05, `foundations.tex`, `def:maximum`. First form the actual-ordinal norm
ball, then retain ordinals below the input, then take its finite supremum.
No notation-domain maximum is used in this definition. Zero on an empty set
is a totalization convention; the source correctness domain is 0 < a < epsilonZero.
No optimized recursion or encoded effectiveness is asserted here.
-/

namespace LogicLineages.OrdinalComparison

noncomputable def actualBoundedPredecessors (a : Ordinal.{0}) (b : Nat) : Finset Ordinal :=
  ((actualFiniteNormBalls b).toFinset).filter (fun x => x < a)

noncomputable def actualMaximumPredecessor (a : Ordinal.{0}) (b : Nat) : Ordinal :=
  (actualBoundedPredecessors a b).sup id

end LogicLineages.OrdinalComparison
