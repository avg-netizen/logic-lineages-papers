module

public import LogicLineages.ComputabilityKnowledge.GorbowPRInternalArithmeticProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRInternalArithmetic.StatementChecks

theorem fullInternalArithmetic : Targets.Target := Proof.fullTarget
theorem actualEvaluation : Targets.ActualEvaluation := fullInternalArithmetic.1
theorem internalAddition : Targets.InternalAddition := fullInternalArithmetic.2.1
theorem internalMultiplication : Targets.InternalMultiplication := fullInternalArithmetic.2.2.1
theorem internalPairing : Targets.InternalPairing := fullInternalArithmetic.2.2.2

end LogicLineages.ComputabilityKnowledge.GorbowPRInternalArithmetic.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowPRInternalArithmetic
