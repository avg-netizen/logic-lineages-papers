module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarRanksStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerConnected.Targets
open CotreeGrammarFlow CotreeGrammarConnected CotreePresburger

/-- The actual formula is exactly the existing connected production-flow
predicate for the requested terminal multiplicities; no reconstruction assumed. -/
def FormulaWordExact : Prop :=
  ∀ (Q : Type) [Fintype Q] [LinearOrder Q] (δ : Q → Q → Q) root (w : List (Finset Q)),
    (formula δ root).Realize (fun B => w.count B) ↔
      ∃ c : Counts Q, Realizes δ root w c ∧ Connected δ root c

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerConnected.Targets
