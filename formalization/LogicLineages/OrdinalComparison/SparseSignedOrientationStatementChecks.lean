module

public import LogicLineages.OrdinalComparison.SparseSignedOrientationProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_sparseSignedNumericalOrientation : LogicLineages.OrdinalComparison.Targets.SparseSignedNumericalOrientation :=
  LogicLineages.OrdinalComparison.sparseSignedNumericalOrientation

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
