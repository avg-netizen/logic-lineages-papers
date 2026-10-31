module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerOrdinalNodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.WalkerOrdinalNodeStatementChecks

theorem coding : Targets.walkerOrdinalCoding := walker_ordinal_coding
theorem children : Targets.walkerOrdinalChildren := walker_ordinal_children
theorem parentHeight : Targets.walkerOrdinalParentHeight := walker_ordinal_parent_height

end LogicLineages.ModelsAlgebra.PGroups.WalkerOrdinalNodeStatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.PGroups.WalkerOrdinalNodeStatementChecks
