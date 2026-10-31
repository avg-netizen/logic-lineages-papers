module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarInitialForestDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarInitialForest.Targets
open CotreeGrammarFlow CotreeGrammarForest

def InitialForestExact : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (δ : Q → Q → Q) (c : Counts Q),
    (∀ B q, q ∉ B → c.terminal (B,q) = 0) → forestCounts (initialForest δ c) = c

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarInitialForest.Targets
