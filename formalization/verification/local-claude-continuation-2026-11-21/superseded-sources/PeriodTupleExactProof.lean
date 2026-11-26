module
public import LogicLineages.CartierObserverCurrent.PeriodDynamicsProof
public import LogicLineages.CartierObserverCurrent.PeriodTupleUpperProof
public import LogicLineages.CartierObserverCurrent.PeriodTupleSmallProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.PeriodTupleFacts
open LogicLineages.OrdinalComparison

theorem actualExact : Targets.ActualExact := by
  intro u hu
  have hr := (actualLinkedResidueArithmetic u (by omega)).1
  exact PeriodDynamics.exactPeriodFromExclusions _ _ _ _ (by omega)
    (actualUpper u hu) (actualMidpoint u hu) (actualSmall u hu)

#audit_namespace LogicLineages.CartierObserverCurrent.PeriodTupleFacts
end LogicLineages.CartierObserverCurrent.PeriodTupleFacts
