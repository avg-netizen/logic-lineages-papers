module

public import LogicLineages.ComputabilityKnowledge.GorbowPRNegativeNumeralsProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRNegativeNumerals.StatementChecks

theorem unequalNumerals : Targets.UnequalNumerals := Proof.unequalNumerals
theorem negativeCalculation : Targets.NegativeCalculation := Proof.negativeCalculation
theorem negativeExactness : Targets.NegativeExactness := Proof.negativeExactness

end LogicLineages.ComputabilityKnowledge.GorbowPRNegativeNumerals.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.GorbowPRNegativeNumerals.StatementChecks
