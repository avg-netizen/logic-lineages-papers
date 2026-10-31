module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealForestDecisionTargets
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealGraphDecisionStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealForestInputStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealForestDecision.Proof
 theorem forestDecisionExact : Targets.ForestDecisionExact := by
  intro U hU
  exact (RankedIdealGraphDecision.StatementChecks.graphDecisionExact
    (RankedIdealForestInput.encode U)).trans
      (RankedIdealForestInput.StatementChecks.forestJEPExact U hU).symm
end LogicLineages.ModelsAlgebra.Forests.RankedIdealForestDecision.Proof
