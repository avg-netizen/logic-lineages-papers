module

public import LogicLineages.ComputabilityKnowledge.OracleJumpDefinitions
public import LogicLineages.ComputabilityKnowledge.OracleRelativeRecursionDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OraclePiTwo
open OracleJump OracleRelativeRecursion

def witnessTest (matrix : Nat × Nat × Nat → Bool) (z : Nat) : Nat :=
  if matrix (z.unpair.1.unpair.1, z.unpair.1.unpair.2, z.unpair.2) then 0 else 1

def witnessSearch (matrix : Nat × Nat × Nat → Bool) : Nat → Part Nat :=
  zeroSearch (witnessTest matrix)

def WitnessCompilerSemantics (matrix : Nat × Nat × Nat → Bool) (code : Nat.Partrec.Code) : Prop :=
  ∀ i x, (code.eval (Nat.pair i x)).Dom ↔ ∃ y, matrix (i, x, y) = true

def counterQuery (code : Nat.Partrec.Code) (z : Nat) : Nat :=
  ordinaryToFirst (Nat.pair (Encodable.encode code) z)

noncomputable def counterTest (code : Nat.Partrec.Code) (z : Nat) : Nat := firstJump (counterQuery code z)

noncomputable def counterSearch (code : Nat.Partrec.Code) : Nat → Part Nat := zeroSearch (counterTest code)

noncomputable def matrixIndicator (matrix : Nat × Nat × Nat → Bool) (i : Nat) : Nat := by
  classical
  exact if ∀ x, ∃ y, matrix (i, x, y) = true then 1 else 0

end LogicLineages.ComputabilityKnowledge.OraclePiTwo
