module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerConnectedStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarInitialForestStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarReconstructStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerGrammar.Targets
open CotreePresburger

/-- The constructed formula is exactly the Parikh image of the literal source
Mathlib context-free grammar. Ordering is not falsely prescribed. -/
def FormulaGrammarExact : Prop :=
  ∀ (Q : Type) [Fintype Q] [LinearOrder Q] (δ : Q → Q → Q) root (w : List (Finset Q)),
    (formula δ root).Realize (fun B => w.count B) ↔
      ∃ v, v ∈ (CotreeGrammar.grammar δ root).language ∧ v.Perm w

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerGrammar.Targets
