module
public import LogicLineages.OrdinalComparison.WWPolicyAssignmentDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open LiteralPolicy
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-- The L policy really extends the existing literal policyPartial, not a replacement
meaning invented for the witness. -/
def ActualLeftPolicyPartialCalibration : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (i : Nat) (t : OrdinalExpression (σ :: Γ)),
    policyPartial .left i t = ordinalTypedPartial i t

/-- Positive coordinates in the repaired source witness, as actual ordinal
values for every valuation (the coordinate is closed). No numerical collapse
is evaluated. This is the displayed 204/184 distinction, not an all-source
policy-independence claim. -/
def ActualClosedSourcePolicySeparation : Prop :=
  ∃ a b : OrdinalExpression [],
    witnessPositive .left = some a ∧ witnessPositive .right = some b ∧
    (∀ ρ, denote ρ a = (204 : Ordinal)) ∧
    (∀ ρ, denote ρ b = (184 : Ordinal)) ∧
    (∀ ρ, denote ρ a ≠ denote ρ b)

end LogicLineages.OrdinalComparison.Source.Targets
