module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerTransitionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerTransition.Targets
open CotreePresburger

def HorizontalFormulaExact : Prop :=
  ∀ (Q A : Type) [Fintype Q] [LinearOrder Q] [Fintype A] [LinearOrder A]
    (δ : Q → Q → Q) (S : Finset Q) (label : A → Finset Q) (allowed : A → Bool)
    (counts : A → Nat),
    (horizontalFormula δ S label allowed).Realize counts ↔
      (∀ q, q ∈ S ↔ (formula δ q).Realize (projectedCounts label counts)) ∧
      2 ≤ ∑ a, counts a ∧ (∀ a, allowed a = false → counts a = 0)

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerTransition.Targets
