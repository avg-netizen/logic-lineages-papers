module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarFlowDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarFlow.Targets

def GrammarFlowNecessary : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (δ : Q → Q → Q) q w,
    w ∈ (CotreeGrammar.grammar δ q).language → ∃ c : Counts Q, Realizes δ q w c

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarFlow.Targets
