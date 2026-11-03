module

public import LogicLineages.ComputabilityKnowledge.GorbowPRInternalControlProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRInternalControl.StatementChecks

theorem fullControl : Targets.Target := Proof.fullTarget
theorem actualEvaluation : Targets.ActualEvaluation := fullControl.1
theorem internalZeroTest : Targets.InternalZeroTest := fullControl.2.1
theorem internalBooleanRange : Targets.InternalBooleanRange := fullControl.2.2.1
theorem internalConditional : Targets.InternalConditional := fullControl.2.2.2

end LogicLineages.ComputabilityKnowledge.GorbowPRInternalControl.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowPRInternalControl
