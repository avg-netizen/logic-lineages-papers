module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedDefiningTheoryDefinitions

@[expose] public section
/-! Literal named source U/u numeral instances in the new uniform alias
theory. These are not axioms of an old total ground diagram. Adequate source
Base/conservativity and internal provability/HB/Lob remain separate. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedNumeralCertificates
open GorbowSyntax

def inputHeader (name : Nat × Nat) (v : List.Vector Nat name.1) : Term 0 :=
  GorbowRegistryTuple.headerTerm name.1 name.2
    (GorbowPRNumeralCalculation.numeralArguments v).toList

def inputCode (name : Nat × Nat) (v : List.Vector Nat name.1) : Nat :=
  GorbowRegistryTuple.header name.1 name.2 v.toList

def functionSentence (name : Nat × Nat) (v : List.Vector Nat name.1) (value : Nat) : Sentence :=
  .equal (.universalFunction (inputHeader name v)) (Term.numeral value)

def relationSentence (name : Nat × Nat) (v : List.Vector Nat name.1) : Sentence :=
  .universalRelation (inputHeader name v)

end LogicLineages.ComputabilityKnowledge.GorbowNamedNumeralCertificates
