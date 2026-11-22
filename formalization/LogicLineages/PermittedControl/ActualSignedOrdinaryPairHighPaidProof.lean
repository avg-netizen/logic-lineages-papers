module
public import LogicLineages.PermittedControl.ActualSignedOrdinaryPairHighTargets
import LogicLineages.PermittedControl.HighFieldComparisonActualProof
import LogicLineages.PermittedControl.ThresholdNoteCodeProof
import LogicLineages.PermittedControl.PreparedParameterActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSignedOrdinaryPairHigh
open OrdinalComparison FieldComparison PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalMatrixLinearRowFormula (choosePolarity)

theorem originalDomain (F : ValueField) (x : Nat) (proper : ProperField F) (paid : normCode F ≤ x) :
    ClosedOrdinaryValueDomain F x := by
  cases F with
  | iterate a => trivial
  | entry a lam mu =>
      change rawNormCode (rawNoteEncode lam.1) ≤ x at paid
      rw [normal_norm_code lam] at paid
      exact ⟨proper,paid⟩

theorem guardedFields (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (F G : ValueField) (hF : ProperField F) (hG : ProperField G)
    (θ : Nat → Nat) (i j : Nat) (paid : minimum B F G ≤ min (θ i) (θ j)) :
    ClosedOrdinaryValueDomain F (θ i) ∧ ClosedOrdinaryValueDomain G (θ j) ∧
    ∃ u v : Nat, LowerOperandActual f θ (.ordinary i F) u ∧
      LowerOperandActual f θ (.ordinary j G) v ∧
      (∀ a b : Nat, FieldValue f F (θ i) a → FieldValue f G (θ j) b → a = u ∧ b = v) := by
  have tail : highFieldComparisonBoundCode B (longFieldCode F) (longFieldCode G) ≤ min (θ i) (θ j) :=
    (le_max_left _ _).trans paid
  have norms : max (normCode F) (normCode G) ≤ min (θ i) (θ j) := (le_max_right _ _).trans paid
  have dF := originalDomain F (θ i) hF ((le_max_left _ _).trans (norms.trans (min_le_left _ _)))
  have dG := originalDomain G (θ j) hG ((le_max_right _ _).trans (norms.trans (min_le_right _ _)))
  obtain ⟨u,v,hu,hv,unique,_⟩ := highFieldComparisonActual f B selected F G hF hG (θ i) (θ j) tail
  exact ⟨dF,dG,u,v,⟨dF,hu⟩,⟨dG,hv⟩,unique⟩

theorem bothLiteralHits (f θ : Nat → Nat) (F G : ValueField) (i j u v : Nat)
    (hu : LowerOperandActual f θ (.ordinary i F) u)
    (hv : LowerOperandActual f θ (.ordinary j G) v) :
    ∃ x y : Nat, lowerOperandRead f θ (.ordinary i F) = some (some x) ∧
      lowerOperandRead f θ (.ordinary j G) = some (some y) :=
  ⟨u,v,(preparedTiedProjection.1 f θ _ u).mpr hu,(preparedTiedProjection.1 f θ _ v).mpr hv⟩

theorem polarityMeaning (base : NormalForm.Formula) (w : Bool) (ν : Nat → Nat) (p : Prop)
    (known : base.eval ν ↔ p) :
    (choosePolarity base w).eval ν ↔ if w then p else ¬p := by
  cases w with
  | false => exact not_congr known
  | true => exact known

end LogicLineages.PermittedControl.ActualSignedOrdinaryPairHigh
