module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualOriginalApplicationInductionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualOriginalApplicationProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication ConfinedStructuralInterpretation SourceConstructorIteration ActualOriginalApplication ActualOriginalApplicationConfinementProof ActualOriginalApplicationInductionProof

theorem successConfinement : ActualOriginalApplicationTargets.SuccessConfinement := by
  intro Symbol inst arity I Γ Δ σ q s hs types τ args ha h r heq
  exact applicationConfined q.val q.property s hs args ha h r heq

theorem successInterpretation : ActualOriginalApplicationTargets.SuccessInterpretation := by
  intro Symbol inst arity I above dec Γ Δ σ q s hs types τ args ha h P ρ η he r hr heq
  exact success above q.val q.property s hs args ha h r hr heq P ρ η he

theorem failureBottom : ActualOriginalApplicationTargets.FailureBottom := by
  intro Symbol inst arity I above dec Γ Δ σ q s hs types τ args ha h P ρ η he heq
  exact failure q.val q.property s args h heq (limit I above) P ρ (argumentValues args ha (limit I above) P η)

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualOriginalApplicationProof
