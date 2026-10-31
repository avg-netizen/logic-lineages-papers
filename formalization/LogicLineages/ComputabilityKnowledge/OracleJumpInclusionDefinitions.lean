module

public import LogicLineages.ComputabilityKnowledge.OracleThirdJumpNormalFormDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OracleJumpInclusion

/-- The existing actual second-jump Sigma2 matrix embedded in Pi3 by an
unused initial universal coordinate. -/
def liftedSecondMatrix (a : Nat × Nat × Nat × Nat) : Bool :=
  OracleThirdJumpNormalForm.secondMatrix a.1 a.2.2.1 a.2.2.2

end LogicLineages.ComputabilityKnowledge.OracleJumpInclusion
