module

public import LogicLineages.ComputabilityKnowledge.GorbowPRNumeralCalculationProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRNumeralCalculation.StatementChecks

theorem numeralCalculation : Targets.NumeralCalculation := Proof.numeralCalculation
theorem numeralExactness : Targets.NumeralExactness := Proof.numeralExactness

end LogicLineages.ComputabilityKnowledge.GorbowPRNumeralCalculation.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowPRNumeralCalculation.StatementChecks
