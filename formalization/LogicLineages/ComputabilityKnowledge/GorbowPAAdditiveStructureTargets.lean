module

public import LogicLineages.ComputabilityKnowledge.GorbowPAAdditiveStructureDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPAAdditiveStructure.Targets
open GorbowSyntax GorbowTheoryProof

def Predecessor : Prop := ∀ T : Sentence → Prop,
  Nonempty (Derivation T GorbowPAAdditiveStructure.predecessor)

def LeftZero : Prop := ∀ T : Sentence → Prop,
  Nonempty (Derivation T GorbowPAAdditiveStructure.leftZero)

def LeftSuccessor : Prop := ∀ T : Sentence → Prop,
  Nonempty (Derivation T GorbowPAAdditiveStructure.leftSuccessor)

def RightCancellation : Prop := ∀ T : Sentence → Prop,
  Nonempty (Derivation T GorbowPAAdditiveStructure.rightCancellation)

def Target : Prop := Predecessor ∧ LeftZero ∧ LeftSuccessor ∧ RightCancellation
end LogicLineages.ComputabilityKnowledge.GorbowPAAdditiveStructure.Targets
