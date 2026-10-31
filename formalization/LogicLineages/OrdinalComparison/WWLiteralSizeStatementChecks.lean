module
public import LogicLineages.OrdinalComparison.WWLiteralSizeProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks

theorem fixed_actualLiteralPartialSizeBound :
    Source.Targets.ActualLiteralPartialSizeBound := Source.actualLiteralPartialSizeBound

theorem fixed_actualLiteralMultiplierBound :
    Source.Targets.ActualLiteralMultiplierBound := Source.actualLiteralMultiplierBound

end LogicLineages.OrdinalComparison.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.Source
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
