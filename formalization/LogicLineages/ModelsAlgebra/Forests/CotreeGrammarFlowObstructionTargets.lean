module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarFlowObstructionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarFlowObstruction.Targets

def FlowIsNotSufficient : Prop :=
  CotreeGrammarFlow.Realizes transition 0 terminalWord circulation ∧
    terminalWord ∉ (CotreeGrammar.grammar transition 0).language

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarFlowObstruction.Targets
