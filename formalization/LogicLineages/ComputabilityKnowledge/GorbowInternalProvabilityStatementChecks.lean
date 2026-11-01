module

public import LogicLineages.ComputabilityKnowledge.GorbowInternalProvabilityProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowInternalProvability.StatementChecks

theorem fullInternalProvability : Targets.Target := Proof.fullTarget

theorem actualCheckerProgram : Targets.CheckerProgram := fullInternalProvability.1
theorem literalSubstitution : Targets.LiteralSubstitution := fullInternalProvability.2.1
theorem numeralCertification : Targets.NumeralCertification := fullInternalProvability.2.2.1
theorem exactStandardSemantics : Targets.ExactStandardSemantics :=
  fullInternalProvability.2.2.2.1
theorem internalCertification : Targets.InternalCertification :=
  fullInternalProvability.2.2.2.2

end LogicLineages.ComputabilityKnowledge.GorbowInternalProvability.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowInternalProvability
