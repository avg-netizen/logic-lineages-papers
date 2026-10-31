module
public import LogicLineages.OrdinalComparison.WWGroundTupleProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.StatementChecks
theorem fixed_groundPositiveTupleComplete : Source.Targets.GroundPositiveTupleComplete := Source.groundPositiveTupleComplete
theorem fixed_groundTuplePositive : Source.Targets.GroundTuplePositive := Source.groundTuplePositive
theorem fixed_emptyContextTupleUnique : Source.Targets.EmptyContextTupleUnique := Source.emptyContextTupleUnique
end LogicLineages.OrdinalComparison.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.StatementChecks
