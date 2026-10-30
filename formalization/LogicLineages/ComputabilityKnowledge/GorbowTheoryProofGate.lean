module

public import LogicLineages.ComputabilityKnowledge.GorbowTheoryProofProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem fixed_gorbowTheoryProof : LogicLineages.ComputabilityKnowledge.Comparators.GorbowTheoryProof.Target :=
  LogicLineages.ComputabilityKnowledge.GorbowTheoryProofProof.gorbowTheoryProof

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
