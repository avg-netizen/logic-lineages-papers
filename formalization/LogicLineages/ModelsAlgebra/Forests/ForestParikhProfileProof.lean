module
public import LogicLineages.ModelsAlgebra.Forests.ForestParikhProfileTargets
public import LogicLineages.ModelsAlgebra.Forests.CotreeMachineParikhStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParikhProfile.Proof
open ProfileAutomatonEncoding

theorem profileFormulaExact : Targets.ProfileFormulaExact := by
  intro F o n c q
  letI : LinearOrder (machine F).State := stateOrder (familyBound F)
  exact CotreeMachineParikh.StatementChecks.stateTransitionExact (machine F) o n c q

end LogicLineages.ModelsAlgebra.Forests.ForestParikhProfile.Proof
