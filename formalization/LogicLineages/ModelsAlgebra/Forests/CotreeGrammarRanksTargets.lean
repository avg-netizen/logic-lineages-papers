module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarRanksDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarRanks.Targets
open CotreeGrammarFlow CotreeGrammarConnected

def RankReachabilityExact : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (δ : Q → Q → Q) root (c : Counts Q),
    (∃ rank : Q → Nat, RankedSupport δ root c rank) ↔ Connected δ root c

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarRanks.Targets
