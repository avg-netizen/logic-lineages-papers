module
public import LogicLineages.OrdinalComparison.SourceObserverPlanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ObserverPlan.StatementChecks
theorem effectiveAnchor : Targets.EffectiveAnchor := Proof.effectiveAnchor
theorem formulaExact : Targets.FormulaExact := Proof.formulaExact
theorem observerExact : Targets.ObserverExact := Proof.observerExact
end LogicLineages.OrdinalComparison.Source.ObserverPlan.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.ObserverPlan
