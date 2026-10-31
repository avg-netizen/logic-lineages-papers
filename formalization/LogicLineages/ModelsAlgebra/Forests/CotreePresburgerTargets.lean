module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburger.Targets
open CotreeGrammarFlow

def FormulaExact : Prop :=
  ∀ (Q : Type) [Fintype Q] [LinearOrder Q] (δ : Q → Q → Q) root (counts : Finset Q → Nat),
    (formula δ root).Realize counts ↔ ∃ c rank, Constraints δ root counts c rank

end LogicLineages.ModelsAlgebra.Forests.CotreePresburger.Targets
