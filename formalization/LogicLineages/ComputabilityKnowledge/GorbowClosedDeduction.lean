module

public import LogicLineages.ComputabilityKnowledge.GorbowTheoryProof

@[expose] public section
/-! Literal extension by a closed sentence. This is a syntactic deduction
supplier for the source S+R / S proving R→φ convention, not a represented
provability predicate or an identification of S with Base/DCB. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowClosedDeduction
open GorbowSyntax

def extend (A : Sentence → Prop) (R : Sentence) : Sentence → Prop :=
  fun σ => A σ ∨ σ = R
end LogicLineages.ComputabilityKnowledge.GorbowClosedDeduction
