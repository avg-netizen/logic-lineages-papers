module

public import LogicLineages.ComputabilityKnowledge.GorbowArithmeticTermCompilerProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowArithmeticTermCompiler.StatementChecks

theorem fullCompiler : Targets.Target := Proof.fullTarget
theorem actualEvaluation : Targets.ActualEvaluation := fullCompiler.1
theorem internalCompiler : Targets.InternalCompiler := fullCompiler.2.1
theorem headerCoverage : Targets.HeaderCoverage := fullCompiler.2.2.1
theorem internalHeaders : Targets.InternalHeaders := fullCompiler.2.2.2

end LogicLineages.ComputabilityKnowledge.GorbowArithmeticTermCompiler.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowArithmeticTermCompiler
