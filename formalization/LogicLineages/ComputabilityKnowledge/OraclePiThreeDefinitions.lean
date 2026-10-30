module

public import LogicLineages.ComputabilityKnowledge.OraclePiTwoDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OraclePiThree
open OracleJump OracleRelativeRecursion

abbrev Matrix := Nat × Nat × Nat × Nat → Bool

noncomputable def thirdJump : Nat → Nat := jump secondJump

def counterMatrix (R : Matrix) (q : Nat × Nat × Nat) : Bool :=
  !(R (q.1.unpair.1, q.1.unpair.2, q.2.1, q.2.2))

noncomputable def counterIndicator (R : Matrix) (q : Nat) : Nat :=
  OraclePiTwo.matrixIndicator (counterMatrix R) q

noncomputable def counterTest (R : Matrix) (q : Nat) : Nat := 1 - counterIndicator R q

noncomputable def counterSearch (R : Matrix) : Nat → Part Nat := zeroSearch (counterTest R)

noncomputable def matrixIndicator (R : Matrix) (i : Nat) : Nat := by
  classical
  exact if ∀ x, ∃ y, ∀ z, R (i, x, y, z) = true then 1 else 0

end LogicLineages.ComputabilityKnowledge.OraclePiThree
