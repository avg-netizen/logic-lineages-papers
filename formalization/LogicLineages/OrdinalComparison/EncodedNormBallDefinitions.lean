module
public import LogicLineages.OrdinalComparison.RawNormalDefinitions
public import LogicLineages.OrdinalComparison.RawNormCodeDefinitions

@[expose] public section

/-! A literal finite numerical enumeration of the normal additive-norm ball.
The bound overestimates every raw code with the given additive norm. A bounded
range is filtered by the explicit numerical NF test and numerical tree norm;
no decidability or search-success assumption is built into the source norm.
The deliberately simple bound is a computability witness, not a practical
complexity bound for the public calculator. -/

namespace LogicLineages.OrdinalComparison

def rawNormCodeBound : Nat → Nat
  | 0 => 0
  | b + 1 => Nat.pair (rawNormCodeBound b) (Nat.pair b (rawNormCodeBound b)) + 1

def encodedNormalNormBall (b : Nat) : List Nat :=
  (List.range (rawNormCodeBound b + 1)).filter
    (fun n => decide (rawNormalCode n = 1 ∧ rawNormCode n ≤ b))

end LogicLineages.OrdinalComparison
