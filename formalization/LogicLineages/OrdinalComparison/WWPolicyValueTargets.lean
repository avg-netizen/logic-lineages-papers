module
public import LogicLineages.OrdinalComparison.WWPolicyAssignmentDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open LiteralPolicy
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-- Exact finite-input output-association clause for the two repaired L/R
policies. This compares partials of the SAME literal tree, never assignments
of the same source under different policies (which can have different trees).
The successful L result is transported to a successful R result with equal
actual ordinal values at every coordinate and valuation. Invalid active shapes
are not assumed admissible. -/
def ActualPolicyFixedInputValue : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (i : Nat) (t : OrdinalExpression (σ :: Γ))
    (v : OrdinalPartialVector Γ σ),
    policyPartial .left i t = some v →
    ∃ w, policyPartial .right i t = some w ∧
      ∀ (j : Fin (σ.level + 2)) (ρ : OrdinalComponent Γ → Ordinal),
        denote ρ (v j) = denote ρ (w j)

end LogicLineages.OrdinalComparison.Source.Targets
