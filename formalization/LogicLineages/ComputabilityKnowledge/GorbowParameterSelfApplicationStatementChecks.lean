module

public import LogicLineages.ComputabilityKnowledge.GorbowParameterSelfApplicationProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowParameterSelfApplication.StatementChecks

theorem fullParameterSelf : Targets.Target := Proof.fullTarget
theorem literalCommutation : Targets.LiteralCommutation := fullParameterSelf.1
theorem numericCalibration : Targets.NumericCalibration := fullParameterSelf.2.1
theorem numericExact : Targets.NumericExact := fullParameterSelf.2.2.1
theorem uniformPrograms : Targets.UniformPrograms := fullParameterSelf.2.2.2.1
theorem programWitness : Targets.ProgramWitness := fullParameterSelf.2.2.2.2

end LogicLineages.ComputabilityKnowledge.GorbowParameterSelfApplication.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowParameterSelfApplication
