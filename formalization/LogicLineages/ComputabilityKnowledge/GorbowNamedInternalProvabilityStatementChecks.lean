module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedInternalProvabilityProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedInternalProvability.StatementChecks

theorem fullNamedInternalProvability : Targets.Target := Proof.fullTarget
theorem preservesEvaluation : Targets.PreservesEvaluation := fullNamedInternalProvability.1
theorem exactCheckerTag : Targets.ExactCheckerTag := fullNamedInternalProvability.2.1
theorem preservesCalibration : Targets.PreservesCalibration := fullNamedInternalProvability.2.2.1
theorem numeralCertificates : Targets.NumeralCertificates := fullNamedInternalProvability.2.2.2.1
theorem literalSubstitution : Targets.LiteralSubstitution := fullNamedInternalProvability.2.2.2.2.1
theorem namedInternalization : Targets.NamedInternalization := fullNamedInternalProvability.2.2.2.2.2.1
theorem exactStandardSemantics : Targets.ExactStandardSemantics := fullNamedInternalProvability.2.2.2.2.2.2

end LogicLineages.ComputabilityKnowledge.GorbowNamedInternalProvability.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowNamedInternalProvability
