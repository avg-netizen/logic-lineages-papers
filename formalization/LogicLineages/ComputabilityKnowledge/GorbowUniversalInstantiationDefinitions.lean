module

public import LogicLineages.ComputabilityKnowledge.GorbowTheoryProof

@[expose] public section
/-! Closed simultaneous instances in the existing Hilbert proof calculus.
This supplier does not add a rule constructor or a semantic-truth premise.
It is needed to turn uniform defining equations into numerical proof objects. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowUniversalInstantiation
open GorbowSyntax

def closedInstance {n : Nat} (phi : Formula n) (sigma : Fin n → Term 0) : Sentence :=
  GorbowFormulaSubstitution.substituteFormula sigma phi

end LogicLineages.ComputabilityKnowledge.GorbowUniversalInstantiation
