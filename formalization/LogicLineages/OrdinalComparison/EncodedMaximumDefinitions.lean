module
public import LogicLineages.OrdinalComparison.EncodedNormBallDefinitions

@[expose] public section

/-! An exhaustive numerical maximum-predecessor algorithm. All comparisons
and finite candidates use the already fixed raw-code algorithms. This supplies
an effective reference maximum, without asserting the optimized simultaneous
recursion of the separate paper-05 maximum theorem. -/

namespace LogicLineages.OrdinalComparison

def largerNormalCode (a b : Nat) : Nat :=
  if rawComparisonCode a b = 0 then b else a

def encodedPredecessorCodes (a budget : Nat) : List Nat :=
  (encodedNormalNormBall budget).filter (fun n => decide (rawComparisonCode n a = 0))

def encodedMaximumPredecessor (a budget : Nat) : Nat :=
  (encodedPredecessorCodes a budget).foldl largerNormalCode 0

end LogicLineages.OrdinalComparison
