module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerTransitionTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerTransition.Proof
open FirstOrder Language CotreePresburger

@[simp] theorem realize_subst {α β : Type} (φ : PFormula α) (f : α → PTerm β)
    (v : β → Nat) : Formula.Realize (φ.subst f) v ↔ φ.Realize (fun a => (f a).realize v) :=
  BoundedFormula.realize_subst

section
variable {Q A : Type} [Fintype Q] [LinearOrder Q] [Fintype A] [LinearOrder A]

@[simp] theorem realize_projectionTerm (label : A → Finset Q) (B : Finset Q)
    (counts : A → Nat) :
    (projectionTerm label B).realize counts = projectedCounts label counts B := by
  simp [projectionTerm, projectedCounts]

@[simp] theorem realize_subsetFormula (δ : Q → Q → Q) (S : Finset Q)
    (counts : Finset Q → Nat) :
    (subsetFormula δ S).Realize counts ↔ ∀ q, q ∈ S ↔ (formula δ q).Realize counts := by
  simp [subsetFormula]

@[simp] theorem realize_totalTerm (counts : A → Nat) :
    (totalTerm (A := A)).realize counts = ∑ a, counts a := by simp [totalTerm]
end

theorem horizontalFormulaExact : Targets.HorizontalFormulaExact := by
  intro Q A _ _ _ _ δ S label allowed counts
  have harity : (0 < ∑ a, counts a ∧ (∑ a, counts a) ≠ 1) ↔ 2 ≤ ∑ a, counts a := by omega
  simp [horizontalFormula, harity, and_assoc]

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerTransition.Proof
