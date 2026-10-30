module

public import LogicLineages.OrdinalComparison.WWCanonicalBoxProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualOrdinalNumeral : LogicLineages.OrdinalComparison.Source.Targets.ActualOrdinalNumeral :=
  LogicLineages.OrdinalComparison.Source.actualOrdinalNumeral

theorem fixed_actualCanonicalBoxEquations : LogicLineages.OrdinalComparison.Source.Targets.ActualCanonicalBoxEquations :=
  LogicLineages.OrdinalComparison.Source.actualCanonicalBoxEquations

theorem fixed_actualCanonicalBoxGeneratedGrade : LogicLineages.OrdinalComparison.Source.Targets.ActualCanonicalBoxGeneratedGrade :=
  LogicLineages.OrdinalComparison.Source.actualCanonicalBoxGeneratedGrade

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
