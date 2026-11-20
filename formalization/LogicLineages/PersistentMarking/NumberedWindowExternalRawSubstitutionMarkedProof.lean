import LogicLineages.PersistentMarking.NumberedWindowExternalRawSubstitutionTargets

namespace LogicLineages.PersistentMarking.NumberedWindowExternalRawSubstitutionMarkedProof
open NumberedWindowSyntax NumberedWindowRules NumberedWindowExternalRawSubstitutionTargets

theorem mark : SubstitutionPreservesMarkDecrease := by
  intro values d q r h
  induction h generalizing d with
  | omega => exact .omega
  | finite h => exact .finite h
  | lam _ ih => exact .lam (ih (d + 1))

private theorem mappedList (values : NArgs) (d : Nat) (xs : NArgs) :
    (substituteArgs values d xs).toList = xs.toList.map (substitute values d) := by
  cases xs with
  | nil => rfl
  | cons a rest => simp only [substituteArgs, NArgs.toList, List.map_cons, mappedList values d rest]
termination_by sizeOf xs

theorem replacement : SubstitutionPreservesPrimitiveReplacement := by
  intro values d source target h
  obtain ⟨kept, removed, added, hSource, hTarget, hNonempty, hDominators⟩ := h
  let op := substitute values d
  refine ⟨kept.map op, removed.map op, added.map op, ?_, ?_, ?_, ?_⟩
  · simpa only [mappedList, List.map_append, op] using hSource.map op
  · simpa only [mappedList, List.map_append, op] using hTarget.map op
  · intro hEmpty
    exact hNonempty (List.map_eq_nil_iff.mp hEmpty)
  · intro a ha
    obtain ⟨before, hb, rfl⟩ := List.mem_map.mp ha
    obtain ⟨origin, ho, hd⟩ := hDominators before hb
    exact ⟨op origin, List.mem_map.mpr ⟨origin, ho, rfl⟩, mark values d origin before hd⟩

end LogicLineages.PersistentMarking.NumberedWindowExternalRawSubstitutionMarkedProof
