module

public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRProgram.StatementChecks

theorem primitiveEvaluation : Targets.PrimitiveEvaluation := Proof.primitiveEvaluation
theorem allPrimitiveFunctions : Targets.AllPrimitiveFunctions := Proof.allPrimitiveFunctions
theorem unaryCorrespondence : Targets.UnaryCorrespondence := Proof.unaryCorrespondence
theorem recursionZero : Targets.RecursionZero := Proof.recursionZero
theorem recursionSuccessor : Targets.RecursionSuccessor := Proof.recursionSuccessor

end LogicLineages.ComputabilityKnowledge.GorbowPRProgram.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowPRProgram.StatementChecks
