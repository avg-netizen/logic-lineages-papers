module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnitProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.StatementChecks

theorem periodPositive : Targets.PeriodPositive := Proof.periodPositive
theorem instantiationExact : Targets.InstantiationExact := Proof.instantiationExact
theorem unitEliminationExact : Targets.UnitEliminationExact := Proof.unitEliminationExact

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.StatementChecks
#audit_namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit
