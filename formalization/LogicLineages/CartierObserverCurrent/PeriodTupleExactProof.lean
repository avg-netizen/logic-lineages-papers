module
public import LogicLineages.CartierObserverCurrent.PeriodTupleFactsTargets
import LogicLineages.CartierObserverCurrent.PeriodDynamicsProof
import LogicLineages.CartierObserverCurrent.PeriodTupleUpperProof
import LogicLineages.CartierObserverCurrent.PeriodTupleSmallProof
import LogicLineages.OrdinalComparison.LinkedResidueProof
public meta import LogicLineages.Audit
public section
namespace LogicLineages.CartierObserverCurrent.PeriodTupleFacts
open LogicLineages.OrdinalComparison

theorem actualExact : Targets.ActualExact := by
  intro u hu
  have hr : 96 ≤ actualLinkedHalfExponent u := (actualLinkedResidueArithmetic u (by omega)).1
  exact PeriodDynamics.exactPeriodFromExclusions _ _ _ _ (by omega)
    (actualUpper u hu) (actualMidpoint u hu) (actualSmall u hu)

#audit_namespace LogicLineages.CartierObserverCurrent.PeriodTupleFacts
end LogicLineages.CartierObserverCurrent.PeriodTupleFacts
