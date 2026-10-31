module

public import LogicLineages.ComputabilityKnowledge.GorbowClassicalDerivationProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowClassicalDerivation.StatementChecks

theorem explosion : Targets.Explosion := Proof.explosion
theorem closedReductio : Targets.ClosedReductio := Proof.closedReductio
theorem doubleNegationElimination : Targets.DoubleNegationElimination := Proof.doubleNegationElimination
theorem modusTollens : Targets.ModusTollens := Proof.modusTollens

end LogicLineages.ComputabilityKnowledge.GorbowClassicalDerivation.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowClassicalDerivation.StatementChecks
