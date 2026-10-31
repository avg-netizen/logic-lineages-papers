module
public import LogicLineages.OrdinalComparison.SourceExistentialPlanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ExistentialPlan.Targets
open GroundEquivalence

def Compilation : Prop := ∀ Γ (q : Plan Γ) (ρ : Variable Γ .ground → Nat),
  Eval ρ q ↔ ∃ ν : Variable (compile q).context .ground → Nat,
    (∀ x, ν ((compile q).embedding x)=ρ x) ∧ (compile q).Holds ν

def Size : Prop := ∀ Γ (q : Plan Γ),
  (compile q).nodes ≤ q.vertices ∧ (compile q).forest.length=q.equations ∧
  (compile q).context.length=Γ.length+q.witnesses ∧
  ((∀ σ ∈ Γ, σ=Ty.ground) → ∀ σ ∈ (compile q).context, σ=Ty.ground)

/-- Finite actual-source PP plan compiler only. The general arithmetic and
Boolean DAG front end is a separate obligation before thm:compiler. -/
def Comparison : Prop := ∀ Γ (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (q : Plan Γ),
  (Strict (strictPair q).1.term (strictPair q).2.term ↔ ¬ ∃ ρ, Eval ρ q) ∧
  (Weak (weakPair q).1.term (weakPair q).2.term ↔ ¬ ∃ ρ, Eval ρ q) ∧
  (strictPair q).1.specs.length ≤ 2*q.vertices+8*q.equations+1 ∧
  (strictPair q).2.specs.length ≤ 2*q.vertices+8*q.equations+1 ∧
  (weakPair q).1.specs.length ≤ 2*q.vertices+8*q.equations+7 ∧
  (weakPair q).2.specs.length ≤ 2*q.vertices+8*q.equations+7
end LogicLineages.OrdinalComparison.Source.ExistentialPlan.Targets
