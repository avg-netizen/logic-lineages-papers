module
public import LogicLineages.PermittedControl.OriginalMatrixUniformHighBoundTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMatrixUniformHighBound
open HeterogeneousSignedMatrixSlice (Row)
open MixedSameRankResidue (WeightedOperand encodeWeighted weightedTailCode)
open OriginalMatrixPaidOrderRow (IsOrder guardBound signBound)

theorem foldCeilingBound {α : Type} (bound : α → Nat) (xs : List α) (x : α) (hx : x ∈ xs) :
    bound x ≤ xs.foldr (fun a n => max (bound a) n) 0 := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with same | later
      · subst x
        exact le_max_left _ _
      · exact (ih later).trans (le_max_right _ _)

private theorem orderPart (B r : Nat) (row : Row) (h : IsOrder row.1) :
    rowCeiling B r row = max (guardBound B r row) (signBound r row) := by
  rcases row with ⟨test,c,ts⟩
  cases test with
  | equalZero => rfl
  | nonnegative => rfl
  | positive => rfl
  | congruence m => cases h

theorem exactUniformHighBound : ExactUniformHighBound := by
  have mem (B r : Nat) (rows : List Row) (row : Row) (h : row ∈ rows) :
      rowCeiling B r row ≤ ceiling B r rows :=
    foldCeilingBound (rowCeiling B r) rows row h
  refine ⟨mem,?_⟩
  intro B r z ρ rows mono paid row hrow
  have rowPaid := (mem B r rows row hrow).trans paid
  refine ⟨?_,?_⟩
  · rcases row with ⟨test,c,ts⟩
    cases test with
    | equalZero => trivial
    | nonnegative => trivial
    | positive => trivial
    | congruence m =>
        intro t ht
        have h := foldCeilingBound (fun u : WeightedOperand => weightedTailCode B m [encodeWeighted u]) ts t ht
        exact h.trans (rowPaid.trans (mono (Nat.zero_le _)))
  · intro h
    rw [orderPart B r row h] at rowPaid
    exact ⟨fun t _ => (le_max_left _ _).trans (rowPaid.trans (mono (Nat.zero_le t.2.rank))),
      (le_max_right _ _).trans (rowPaid.trans (mono (Nat.zero_le z)))⟩

end LogicLineages.PermittedControl.OriginalMatrixUniformHighBound
