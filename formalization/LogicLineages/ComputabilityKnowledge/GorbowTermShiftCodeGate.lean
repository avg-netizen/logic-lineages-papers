module

public import LogicLineages.ComputabilityKnowledge.GorbowTermShiftCodeProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem gorbow_term_shift_code : LogicLineages.ComputabilityKnowledge.Comparators.GorbowTermShiftCode.Target :=
  LogicLineages.ComputabilityKnowledge.GorbowTermShiftCodeProof.gorbowTermShiftCode

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
