module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarFlowObstructionTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarFlowObstruction.Proof

theorem flowIsNotSufficient : Targets.FlowIsNotSufficient := by
  constructor
  · unfold CotreeGrammarFlow.Realizes
    decide
  · intro h
    have hb := (CotreeGrammar.StatementChecks.grammarLanguageExact (Fin 3) transition 0 terminalWord).mp h
    cases hb

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarFlowObstruction.Proof
