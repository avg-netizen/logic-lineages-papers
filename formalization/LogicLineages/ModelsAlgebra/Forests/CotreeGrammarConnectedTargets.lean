module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarConnectedDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarConnected.Targets

def ConnectedFlowNecessary : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (δ : Q → Q → Q) q w,
    w ∈ (CotreeGrammar.grammar δ q).language →
      ∃ c : CotreeGrammarFlow.Counts Q, CotreeGrammarFlow.Realizes δ q w c ∧ Connected δ q c

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarConnected.Targets
