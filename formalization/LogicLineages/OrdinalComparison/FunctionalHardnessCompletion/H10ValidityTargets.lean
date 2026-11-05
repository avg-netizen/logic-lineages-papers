module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.H10ValidityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.H10Validity.Targets
open LogicLineages.ComputabilityKnowledge.PolynomialCircuit

def VariablesValidity : Prop := ∀ (n : Nat) (vs : List Nat),
  variablesValid n vs = true ↔ ∀ i ∈ vs, i < n

def TermsValidity : Prop := ∀ (n : Nat) (ms : Monomials),
  termsValid n ms = true ↔ ∀ m ∈ ms, ∀ i ∈ m.2, i < n

/-- Exact recognition on arbitrary raw input lists, not merely canonical codes. -/
def InputValidity : Prop := ∀ xs : List Nat,
  validInput xs = true ↔ ∃ p : Code,
    LogicLineages.ComputabilityKnowledge.PolynomialCircuit.decode xs = some p ∧ p.WellFormed

def CanonicalValidity : Prop := ∀ p : Code,
  validInput (LogicLineages.ComputabilityKnowledge.PolynomialCircuit.encode p) = true ↔ p.WellFormed

/-- The numeric endpoint uses only the global List Nat and Bool encodings. -/
def ValidityPrimitive : Prop := Primrec validInput

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.H10Validity.Targets
