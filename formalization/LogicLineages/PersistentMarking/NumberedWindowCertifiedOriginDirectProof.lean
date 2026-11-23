module
public import LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginDirectTargets
import LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginConsumptionProof
import LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginRowsProof
import Init.Data.List.Lemmas

public section
namespace LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginDirectProof
open NumberedWindowDirectAlgorithm (Entry directLists)
open NumberedWindowCertifiedOriginDirectTargets (ExactNumericOriginDirectCases)
open NumberedWindowCertifiedOriginConsumptionProof (exact_OriginConsumption)
open NumberedWindowCertifiedOriginRowsTargets (RowFit)
open NumberedWindowCertifiedOriginRowsProof (exact_OriginRowAssignment exact_OriginTargetRecombination)

private theorem typedSides (scalar : Nat → Bool) {u left right : List Nat}
    (typed : u.all scalar = true) (joined : u.Perm (left ++ right)) :
    left.all scalar = true ∧ right.all scalar = true := by
  constructor
  · exact List.all_eq_true.mpr (fun n h => List.all_eq_true.mp typed n
      (joined.mem_iff.mpr (List.mem_append_left right h)))
  · exact List.all_eq_true.mpr (fun n h => List.all_eq_true.mp typed n
      (joined.mem_iff.mpr (List.mem_append_right left h)))

private theorem checkedSide (scalar : Nat → Bool) (positive : Nat → Nat → Nat → Bool)
    {source kept removed : List Nat} {rows : List Entry}
    (hs : source.all scalar = true) (ht : (kept ++ rows.map Prod.fst).all scalar = true)
    (hsrc : source.Perm (kept ++ removed)) (hne : removed ≠ [])
    (hrows : RowFit positive removed rows) :
    directLists scalar positive source (kept ++ rows.map Prod.fst) (kept, removed, rows) = true := by
  simp only [directLists, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true]
  exact ⟨⟨⟨⟨⟨List.all_eq_true.mp hs, List.all_eq_true.mp ht⟩, hsrc⟩,
    List.Perm.rfl⟩, hne⟩, hrows⟩

private theorem rejoinUnchanged {positive : Nat → Nat → Nat → Bool}
    {source kept removed : List Nat} {rows : List Entry}
    (hn : removed = []) (hr : RowFit positive removed rows)
    (hsrc : source.Perm (kept ++ removed)) :
    (kept ++ rows.map Prod.fst).Perm source := by
  have rowsEmpty : rows = [] := by
    cases rows with
    | nil => rfl
    | cons e es =>
      have hit := (hr e List.mem_cons_self).1
      exact False.elim (List.not_mem_nil (hn ▸ hit))
  simpa only [hn, rowsEmpty, List.map_nil, List.append_nil] using hsrc.symm

theorem exact_NumericOriginDirectCases : ExactNumericOriginDirectCases := by
  intro scalar positive left right source target w joined checked
  rcases w with ⟨kept, removed, rows⟩
  simp only [directLists, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', List.isEmpty_eq_false_iff] at checked
  obtain ⟨⟨⟨⟨⟨sTyped,tTyped⟩,sSplit⟩,tSplit⟩,nonempty⟩,fit⟩ := checked
  have originalRows : RowFit positive removed rows := by
    intro e he
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using (List.all_eq_true.mp fit e he)
  obtain ⟨kl, kr, rl, rr, lSplit, rSplit, kSplit, remSplit⟩ :=
    exact_OriginConsumption left right kept removed (joined.symm.trans sSplit)
  obtain ⟨al, ar, aSplit, aLeft, aRight⟩ :=
    exact_OriginRowAssignment positive removed rl rr rows remSplit originalRows
  have targetJoined :=
    exact_OriginTargetRecombination target kept kl kr rows al ar tSplit kSplit aSplit
  obtain ⟨sLeft,sRight⟩ := typedSides scalar sTyped joined
  obtain ⟨tLeft,tRight⟩ := typedSides scalar tTyped targetJoined
  by_cases emptyLeft : rl = []
  · have nonemptyRight : rr ≠ [] := by
      intro emptyRight
      apply nonempty
      exact (by simpa only [emptyLeft, emptyRight, List.nil_append] using remSplit : removed.Perm []).eq_nil
    have rightChecked := checkedSide scalar positive sRight tRight rSplit nonemptyRight aRight
    have leftSame := rejoinUnchanged emptyLeft aLeft lSplit
    exact Or.inr (Or.inl ⟨kr ++ ar.map Prod.fst, (kr, rr, ar), rightChecked,
      targetJoined.trans (leftSame.append_right _)⟩)
  · have leftChecked := checkedSide scalar positive sLeft tLeft lSplit emptyLeft aLeft
    by_cases emptyRight : rr = []
    · have rightSame := rejoinUnchanged emptyRight aRight rSplit
      exact Or.inl ⟨kl ++ al.map Prod.fst, (kl, rl, al), leftChecked,
        targetJoined.trans (rightSame.append_left _)⟩
    · have rightChecked := checkedSide scalar positive sRight tRight rSplit emptyRight aRight
      exact Or.inr (Or.inr ⟨kl ++ al.map Prod.fst, kr ++ ar.map Prod.fst,
        (kl, rl, al), (kr, rr, ar), leftChecked, rightChecked, targetJoined⟩)

#print axioms exact_NumericOriginDirectCases

end LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginDirectProof
