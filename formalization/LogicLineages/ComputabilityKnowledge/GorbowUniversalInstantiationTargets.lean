module

public import LogicLineages.ComputabilityKnowledge.GorbowUniversalInstantiationDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowUniversalInstantiation.Targets
open GorbowSyntax GorbowTheoryProof GorbowStandardInduction

def UniversalSpecialization : Prop := ∀ (A : Sentence → Prop) n (phi : Formula n)
    (sigma : Fin n → Term 0), Derivation A (universalClosure phi) →
  Nonempty (Derivation A (closedInstance phi sigma))

def AxiomSpecialization : Prop := ∀ (A : Sentence → Prop) n (phi : Formula n)
    (sigma : Fin n → Term 0), A (universalClosure phi) →
  Nonempty (Derivation A (closedInstance phi sigma))

end LogicLineages.ComputabilityKnowledge.GorbowUniversalInstantiation.Targets
