module

public import LogicLineages.OrdinalComparison.BinaryPeriodSuppliersProof
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualFermatShapeTwoOrder : LogicLineages.OrdinalComparison.Targets.ActualFermatShapeTwoOrder :=
  LogicLineages.OrdinalComparison.actualFermatShapeTwoOrder

theorem fixed_actualBinarySourceReciprocity : LogicLineages.OrdinalComparison.Targets.ActualBinarySourceReciprocity :=
  LogicLineages.OrdinalComparison.actualBinarySourceReciprocity

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison
