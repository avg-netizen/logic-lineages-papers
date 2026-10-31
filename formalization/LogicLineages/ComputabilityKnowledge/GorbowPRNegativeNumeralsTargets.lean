module

public import LogicLineages.ComputabilityKnowledge.GorbowPRNegativeNumeralsDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRNegativeNumerals.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations
open GorbowPRNumeralCalculation GorbowTheoryProof

def UnequalNumerals : Prop := ∀ (A : Sentence → Prop) (a b : Nat), a ≠ b →
  Nonempty (Derivation (n:=0) A (.neg (.equal (Term.numeral a) (Term.numeral b))))

def NegativeCalculation : Prop := ∀ n (p : Program n) (tag : Nat) m (q : Program m),
  (nodes p)[tag]? = some ⟨m,q⟩ → ∀ (v : List.Vector Nat m) (value : Nat),
    evaluate q v ≠ value → Nonempty (Derivation (Theory p)
      (.neg (.equal (call tag (numeralArguments v)) (Term.numeral value))))

def NegativeExactness : Prop := ∀ n (p : Program n) (tag : Nat) m (q : Program m),
  (nodes p)[tag]? = some ⟨m,q⟩ → ∀ (v : List.Vector Nat m) (value : Nat),
    Nonempty (Derivation (Theory p)
      (.neg (.equal (call tag (numeralArguments v)) (Term.numeral value)))) ↔ evaluate q v ≠ value

end LogicLineages.ComputabilityKnowledge.GorbowPRNegativeNumerals.Targets
