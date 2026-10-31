module
public import LogicLineages.OrdinalComparison.SourceExistentialPlanComparisonProof
public import LogicLineages.OrdinalComparison.SourceExistentialPlanSizeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ExistentialPlan.Proof
theorem comparison : Targets.Comparison := by
  intro Γ hΓ q
  exact ⟨strict_unsat q,weak_unsat q ((size Γ q).2.2.2 hΓ),pair_size_bounds Γ q⟩
end LogicLineages.OrdinalComparison.Source.ExistentialPlan.Proof
