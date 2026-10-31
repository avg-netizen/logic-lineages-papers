module
public import LogicLineages.OrdinalComparison.WWScalarPolicyWitnessDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open LiteralPolicy LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def ActualScalarWitnessPolynomialSound : Prop :=
  ∀ (Γ : List Ty) (t : OrdinalExpression Γ) (a : WitnessPolynomial),
    witnessPolynomial t = some a → ∀ ρ : OrdinalComponent Γ → Ordinal,
      denote ρ t = (a.value : Ordinal)

/-- The printed actual scalar L/R formulas and strict distinction for the same
literal typed closed source used by the accepted 204/184 positive-coordinate
witness. No beta normalization or numerical collapse evaluation is allowed. -/
def ActualClosedScalarPolicySeparation : Prop :=
  ∃ a b : OrdinalExpression [],
    witnessScalar .left = some a ∧ witnessScalar .right = some b ∧
    (∀ ρ, denote ρ a =
      ((388 * (10 * witnessH 20 + witnessH 14 + 10) + 10 * witnessH 8 + witnessH 6 : Nat) : Ordinal)) ∧
    (∀ ρ, denote ρ b =
      ((348 * (10 * witnessH 18 + witnessH 14 + 10) + 10 * witnessH 8 + witnessH 6 : Nat) : Ordinal)) ∧
    (∀ ρ, denote ρ b < denote ρ a)

end LogicLineages.OrdinalComparison.Source.Targets
