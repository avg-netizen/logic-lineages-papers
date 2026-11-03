module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalDerivationBudgetCompletenessProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OriginalDerivationBudgetProof
open OriginalDerivationBudgetCompletenessProof OriginalDerivationBudgetErasureProof

theorem actualFiveWayEquivalence : OriginalDerivationBudgetTargets.ActualFiveWayEquivalence := by
  intro Symbol arity above
  exact ⟨fun _ _ _ => ⟨fun h => weakComplete above h,fun ⟨n,h⟩ => weakSound h⟩,
    fun _ _ _ => ⟨fun h => strictComplete above h,fun ⟨n,h⟩ => strictSound h⟩,
    fun _ _ _ => ⟨fun h => matchComplete above h,fun ⟨n,h⟩ => matchSound h⟩,
    fun _ _ _ => ⟨fun h => multisetComplete above h,fun ⟨n,h⟩ => multisetSound h⟩,
    fun _ _ _ => ⟨fun h => replacementComplete above h,fun ⟨n,h⟩ => replacementSound h⟩⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.OriginalDerivationBudgetProof
