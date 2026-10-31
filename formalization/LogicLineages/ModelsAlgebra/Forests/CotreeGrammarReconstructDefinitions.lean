module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarNormalStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarRanksStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarProductionStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarInsertionStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarReconstruct
open CotreeGrammarForest

def rankSum {Q : Type} {δ : Q → Q → Q} (rank : Q → Nat) (F : List (Packed δ)) : Nat :=
  (F.map (fun t => rank t.1)).sum

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarReconstruct
