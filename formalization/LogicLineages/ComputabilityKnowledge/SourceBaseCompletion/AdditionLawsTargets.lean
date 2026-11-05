module

public import LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.AdditionLawsDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.AdditionLaws.Targets
open GorbowSyntax GorbowTheoryProof

def Associativity : Prop := ∀ T : Sentence → Prop,
  Nonempty (Derivation T AdditionLaws.associativity)

def Commutativity : Prop := ∀ T : Sentence → Prop,
  Nonempty (Derivation T AdditionLaws.commutativity)

def LeftZeroOfSumZero : Prop := ∀ T : Sentence → Prop,
  Nonempty (Derivation T AdditionLaws.leftZeroOfSumZero)

def Target : Prop := Associativity ∧ Commutativity ∧ LeftZeroOfSumZero

end LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.AdditionLaws.Targets
