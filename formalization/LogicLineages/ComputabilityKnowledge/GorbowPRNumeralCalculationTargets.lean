module

public import LogicLineages.ComputabilityKnowledge.GorbowPRNumeralCalculationDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRNumeralCalculation.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof

def NumeralCalculation : Prop := ∀ n (p : Program n) (tag : Nat) m (q : Program m),
  (nodes p)[tag]? = some ⟨m,q⟩ → ∀ v : List.Vector Nat m,
    Nonempty (Derivation (Theory p)
      (.equal (call tag (numeralArguments v)) (Term.numeral (evaluate q v))))

def NumeralExactness : Prop := ∀ n (p : Program n) (tag : Nat) m (q : Program m),
  (nodes p)[tag]? = some ⟨m,q⟩ → ∀ (v : List.Vector Nat m) (value : Nat),
    Nonempty (Derivation (Theory p)
      (.equal (call tag (numeralArguments v)) (Term.numeral value))) ↔ evaluate q v = value

end LogicLineages.ComputabilityKnowledge.GorbowPRNumeralCalculation.Targets
