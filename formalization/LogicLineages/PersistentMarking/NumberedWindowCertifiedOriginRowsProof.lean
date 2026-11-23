module
public import LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginRowsTargets
import Init.Data.List.Lemmas

public section
namespace LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginRowsProof
open NumberedWindowDirectAlgorithm (Entry)
open NumberedWindowCertifiedOriginRowsTargets (ExactOriginRowAssignment ExactOriginTargetRecombination RowFit)

private theorem rowFitNil (positive : Nat → Nat → Nat → Bool) (removed : List Nat) :
    RowFit positive removed [] :=
  fun _ h => False.elim (List.not_mem_nil h)

private theorem rowFitCons {positive : Nat → Nat → Nat → Bool} {removed : List Nat}
    {e : Entry} {rows : List Entry} (head : e.2.1 ∈ removed ∧ positive e.2.1 e.2.2 e.1 = true)
    (tail : RowFit positive removed rows) : RowFit positive removed (e :: rows) := by
  intro q hq
  rcases List.mem_cons.mp hq with equal | inTail
  · subst q
    exact head
  · exact tail q inTail

/-- A removed dominator is queried but never consumed. Each original row
occurrence, including its unchanged positive certificate field, goes to one side. -/
theorem exact_OriginRowAssignment : ExactOriginRowAssignment := by
  intro positive removed removedLeft removedRight rows split
  induction rows with
  | nil =>
    intro _
    exact ⟨[], [], List.Perm.rfl, rowFitNil _ _, rowFitNil _ _⟩
  | cons e rows ih =>
    intro fit
    obtain ⟨inRemoved, checked⟩ := fit e List.mem_cons_self
    have located : e.2.1 ∈ removedLeft ∨ e.2.1 ∈ removedRight :=
      List.mem_append.mp (split.mem_iff.mp inRemoved)
    obtain ⟨rowsLeft, rowsRight, hperm, hleft, hright⟩ :=
      ih (fun q hq => fit q (List.mem_cons_of_mem e hq))
    by_cases onLeft : e.2.1 ∈ removedLeft
    · exact ⟨e :: rowsLeft, rowsRight, hperm.cons e, rowFitCons ⟨onLeft, checked⟩ hleft,
        hright⟩
    · have onRight := located.resolve_left onLeft
      have recombine : (e :: (rowsLeft ++ rowsRight)).Perm (rowsLeft ++ e :: rowsRight) :=
        List.perm_middle.symm
      exact ⟨rowsLeft, e :: rowsRight, (hperm.cons e).trans recombine, hleft,
        rowFitCons ⟨onRight, checked⟩ hright⟩

/-- Project the unchanged target field of each whole row, and move the
right kept tape past the left inserted entries. -/
theorem exact_OriginTargetRecombination : ExactOriginTargetRecombination := by
  intro target kept keptLeft keptRight rows rowsLeft rowsRight dst split rowSplit
  have projected : (rows.map Prod.fst).Perm (rowsLeft.map Prod.fst ++ rowsRight.map Prod.fst) := by
    simpa only [List.map_append] using rowSplit.map (Prod.fst : Entry → Nat)
  have shuffle :
      ((keptLeft ++ keptRight) ++ (rowsLeft.map Prod.fst ++ rowsRight.map Prod.fst)).Perm
        ((keptLeft ++ rowsLeft.map Prod.fst) ++ (keptRight ++ rowsRight.map Prod.fst)) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm_assoc keptRight (rowsLeft.map Prod.fst) (rowsRight.map Prod.fst)).append_left
        keptLeft
  exact dst.trans ((split.append projected).trans shuffle)

#print axioms exact_OriginRowAssignment
#print axioms exact_OriginTargetRecombination

end LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginRowsProof
