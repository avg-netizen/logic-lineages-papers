module

public import LogicLineages.ComputabilityKnowledge.GorbowDerivationSubstitutionProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowDerivationSubstitution.StatementChecks

theorem fullSubstitution : Targets.Target := Proof.fullTarget
theorem instantiationNaturality : Targets.InstantiationNaturality := fullSubstitution.1
theorem logicalInstances : Targets.LogicalInstances := fullSubstitution.2.1
theorem arithmeticInstances : Targets.ArithmeticInstances := fullSubstitution.2.2.1
theorem derivationSubstitution : Targets.DerivationSubstitution := fullSubstitution.2.2.2.1
theorem closedLifting : Targets.ClosedLifting := fullSubstitution.2.2.2.2

end LogicLineages.ComputabilityKnowledge.GorbowDerivationSubstitution.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowDerivationSubstitution
