module
public import LogicLineages.CartierObserverCurrent.PeriodTupleExistenceProof
public import LogicLineages.OrdinalComparison.ResidueFrobeniusProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.PeriodTupleFacts
open LogicLineages.OrdinalComparison

theorem actualUpper : Targets.ActualUpper := by
  intro u hu
  funext z
  rw [actualIterate]
  exact actualResidueFrobeniusUpperPeriod ActualResidueField u hu z.val z.property

theorem actualMidpoint : Targets.ActualMidpoint := by
  intro u hu h
  obtain ⟨z⟩ := rootExists u hu
  have hz := congrFun h z
  rw [actualIterate] at hz
  exact actualResidueFrobeniusMidpointNonfixed ActualResidueField u hu z.val z.property hz

#audit_namespace LogicLineages.CartierObserverCurrent.PeriodTupleFacts
end LogicLineages.CartierObserverCurrent.PeriodTupleFacts
