module

public import LogicLineages.OrdinalComparison.ActualOrdinalNorm
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actual_norm_equation : Targets.ActualNormCNFEquation actualOrdinalNorm :=
  actualOrdinalNorm_cnfEquation

theorem fixed_actual_norm_uniqueness : Targets.ActualNormUniqueBelowEpsilonZero actualOrdinalNorm :=
  actualOrdinalNorm_uniqueBelowEpsilonZero

theorem fixed_actual_norm_notation_correspondence :
    Targets.ActualNormNotationCorrespondence actualOrdinalNorm :=
  actualOrdinalNorm_notationCorrespondence

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
