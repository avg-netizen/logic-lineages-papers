module

public import LogicLineages.OrdinalComparison.SparseSignedNumericalProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_sparseSignedNumericalNonzero : LogicLineages.OrdinalComparison.Targets.SparseSignedNumericalNonzero :=
  LogicLineages.OrdinalComparison.sparseSignedNumericalNonzero

theorem fixed_phiPreviousProductGap : LogicLineages.OrdinalComparison.Targets.PhiPreviousProductGap :=
  LogicLineages.OrdinalComparison.phiPreviousProductGap

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
