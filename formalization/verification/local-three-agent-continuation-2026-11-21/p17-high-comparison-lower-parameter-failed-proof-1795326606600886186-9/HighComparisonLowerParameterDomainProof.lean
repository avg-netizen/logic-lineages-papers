module
public import LogicLineages.PermittedControl.HighComparisonLowerParameterTargets

@[expose] public section
namespace LogicLineages.PermittedControl.HighComparisonLowerParameter
open OrdinalComparison FieldComparison

private theorem reflectedEntryHead {sign sign' a a' : Nat} {lam mu lam' mu' : NONote}
    (same : ComparisonForm.linear sign (.entry a lam mu) =
      .linear sign' (.entry a' lam' mu')) : lam = lam' := by
  injection same with _ fields
  injection fields with _ head _
  exact head

theorem smallerEntryHeadExact : SmallerEntryHeadExact := by
  intro F G sign a lam mu form
  cases F with
  | iterate m =>
    cases G with
    | iterate n =>
      by_cases ordered : m ≤ n <;> simp [distinctForm,ordered] at form
    | entry b rightLam rightMu =>
      simp [distinctForm] at form
  | entry outer leftLam leftMu =>
    have same : leftLam = lam := by
      cases G with
      | iterate n =>
        by_cases ordered : n ≤ outer
        · apply reflectedEntryHead
          simpa only [distinctForm,if_pos ordered] using form
        · apply reflectedEntryHead
          simpa only [distinctForm,if_neg ordered] using form
      | entry b rightLam rightMu =>
        cases order : NONote.cmp (rightLam - (rightMu + omegaMultiple (outer - b)))
            (leftLam - (leftMu + omegaMultiple (b - outer))) with
        | lt =>
          apply reflectedEntryHead
          simpa only [distinctForm,order] using form
        | eq => simp [distinctForm,order] at form
        | gt => simp [distinctForm,order] at form
    subst leftLam
    exact ⟨outer,leftMu,rfl⟩

private theorem headBelowPeel (B : Nat) (lam mu : NONote) (c : Nat) :
    actualOrdinalNorm lam.1.repr ≤ longFieldPeelBound B lam mu c := by
  unfold longFieldPeelBound
  exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))

private theorem headBelowDistinct (B a : Nat) (lam mu : NONote) (G : ValueField) :
    actualOrdinalNorm lam.1.repr ≤ longFieldDistinctBound B (.entry a lam mu) G := by
  cases G with
  | iterate n =>
    exact (headBelowPeel B lam mu 0).trans (le_max_left _ _)
  | entry b rightLam rightMu =>
    exact (headBelowPeel B lam mu (b - a)).trans ((le_max_left _ _).trans (le_max_left _ _))

theorem affordableLowerParameter : AffordableLowerParameter := by
  intro B F G H sign x form proper bound
  cases H with
  | iterate a => exact True.intro
  | entry a lam mu =>
    obtain ⟨outer,originalLower,rfl⟩ := smallerEntryHeadExact F G sign a lam mu form
    exact ⟨proper,(headBelowDistinct B outer lam originalLower G).trans bound⟩

end LogicLineages.PermittedControl.HighComparisonLowerParameter
