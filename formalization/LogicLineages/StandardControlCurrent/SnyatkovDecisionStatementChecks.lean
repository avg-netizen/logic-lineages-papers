module
public import LogicLineages.StandardControlCurrent.SnyatkovDecisionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.StandardControlCurrent.SnyatkovDecisionStatementChecks

theorem controlArithmetic : SnyatkovDecisionTargets.ControlArithmetic :=
  SnyatkovDecisionProof.controlArithmetic

theorem currentBinderCompatibility : SnyatkovDecisionTargets.CurrentBinderCompatibility :=
  SnyatkovDecisionProof.currentBinderCompatibility

theorem effectiveOriginalElimination : SnyatkovDecisionTargets.EffectiveOriginalElimination :=
  SnyatkovDecisionProof.effectiveOriginalElimination

theorem zeroEvaluator : SnyatkovDecisionTargets.ZeroEvaluator :=
  SnyatkovDecisionProof.zeroEvaluator

theorem actualClosedAnswer : SnyatkovDecisionTargets.ActualClosedAnswer :=
  SnyatkovDecisionProof.actualClosedAnswer

theorem fullSourceDecision : SnyatkovDecisionTargets.FullSourceDecision :=
  SnyatkovDecisionProof.fullSourceDecision

#print axioms controlArithmetic
#print axioms currentBinderCompatibility
#print axioms effectiveOriginalElimination
#print axioms zeroEvaluator
#print axioms actualClosedAnswer
#print axioms fullSourceDecision
end LogicLineages.StandardControlCurrent.SnyatkovDecisionStatementChecks
#audit_namespace LogicLineages.StandardControlCurrent.SnyatkovDecisionStatementChecks
