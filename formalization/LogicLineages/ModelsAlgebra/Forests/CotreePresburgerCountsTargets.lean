module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCountsDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCounts.Targets
open CotreePresburger

def WordCountsExact : Prop :=
  ∀ (Q : Type) [Fintype Q] [LinearOrder Q] (counts : Finset Q → Nat) B,
    (wordOfCounts counts).count B = counts B

/-- Full Parikh semantics for every free count vector, not just counts of an
already supplied word. The formula compiler is executable; no QE asserted. -/
def FormulaCountsExact : Prop :=
  ∀ (Q : Type) [Fintype Q] [LinearOrder Q] (δ : Q → Q → Q) root (counts : Finset Q → Nat),
    (formula δ root).Realize counts ↔
      ∃ w, w ∈ (CotreeGrammar.grammar δ root).language ∧ ∀ B, w.count B = counts B

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCounts.Targets
