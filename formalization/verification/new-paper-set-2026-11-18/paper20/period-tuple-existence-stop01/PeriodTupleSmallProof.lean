module
public import LogicLineages.CartierObserverCurrent.PeriodTupleExistenceProof
public import LogicLineages.OrdinalComparison.ResidueRootCountProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.PeriodTupleFacts
open LogicLineages.OrdinalComparison

theorem actualSmall : Targets.ActualSmall := by
  intro u hu s hs hsr hper
  obtain ⟨z₀⟩ := rootExists u hu
  obtain ⟨z, hz, hnf⟩ := actualResidueSmallExponentNonfixed ActualResidueField u s hu
    hs hsr z₀.val z₀.property
  have h := congrFun hper ⟨z, hz⟩
  rw [actualIterate] at h
  exact hnf h

#audit_namespace LogicLineages.CartierObserverCurrent.PeriodTupleFacts
end LogicLineages.CartierObserverCurrent.PeriodTupleFacts
