module
public import LogicLineages.OrdinalComparison.WWScopedSourceDAGProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ScopedDAG.StatementChecks
theorem «renaming» : Targets.Renaming := Proof.renaming
theorem application : Targets.Application := Proof.application
theorem eraser : Targets.Eraser := Proof.eraser
theorem aggregate : Targets.Aggregate := Proof.aggregate
end LogicLineages.OrdinalComparison.Source.ScopedDAG.StatementChecks
#audit_namespace LogicLineages.OrdinalComparison.Source.ScopedDAG
