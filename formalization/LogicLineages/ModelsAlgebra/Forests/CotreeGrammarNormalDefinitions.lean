module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarForestStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarNormal
open CotreeGrammarForest

def Balanced {Q : Type} [DecidableEq Q] {δ : Q → Q → Q} (root : Q)
    (F : List (Packed δ)) : Prop :=
  ∀ q, (roots F).count q = (forestHoles F).count q + if root = q then 1 else 0

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarNormal
