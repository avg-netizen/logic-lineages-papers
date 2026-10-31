module

public import LogicLineages.ComputabilityKnowledge.GorbowPRDefiningEquationsDefinitions

@[expose] public section
/-! Actual numeral calculation specifications for finite PR defining theories.
These are existing Hilbert derivations, not semantic-truth certificates or
an assumed representation field. Selecting the source syntactic programs,
adequate source Base and internal HB/Lob still remain separate obligations. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPRNumeralCalculation
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations

def numeralArguments {n : Nat} (v : List.Vector Nat n) : List.Vector (Term 0) n :=
  v.map Term.numeral

def Theory {n : Nat} (p : Program n) : Sentence → Prop := fun sigma => sigma ∈ axioms p

end LogicLineages.ComputabilityKnowledge.GorbowPRNumeralCalculation
