import LogicLineages.PersistentMarking.NumberedWindowArithmeticOccurrencePartitionTargets

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticKeptRemovedOriginProof
open NumberedWindowArithmeticOccurrencePartitionTargets

/-- Moving the original tagged entries through each adjacent swap keeps
the component of origin even when the swapped values agree. -/
private theorem transportOrigins {xs ys : List Nat} (h : xs.Perm ys) :
    ∀ tagged : List (Sum Nat Nat), tagged.map forgetOrigin = xs →
      ∃ reordered, tagged.Perm reordered ∧ reordered.map forgetOrigin = ys := by
  induction h with
  | nil =>
    intro tagged hValues
    exact ⟨tagged, .rfl, hValues⟩
  | cons x _ ih =>
    intro tagged hValues
    cases tagged with
    | nil => cases hValues
    | cons entry rest =>
      obtain ⟨hEntry, hRest⟩ := List.cons.inj hValues
      obtain ⟨reordered, hPerm, hMap⟩ := ih rest hRest
      exact ⟨entry :: reordered, .cons entry hPerm, by simp only [List.map_cons, hEntry, hMap]⟩
  | swap x y xs =>
    intro tagged hValues
    cases tagged with
    | nil => cases hValues
    | cons first rest =>
      cases rest with
      | nil => cases hValues
      | cons second tail =>
        obtain ⟨hFirst, hRest⟩ := List.cons.inj hValues
        obtain ⟨hSecond, hTail⟩ := List.cons.inj hRest
        exact ⟨second :: first :: tail, .swap second first tail,
          by simp only [List.map_cons, hFirst, hSecond, hTail]⟩
  | trans _ _ ih₁ ih₂ =>
    intro tagged hValues
    obtain ⟨middle, hFirst, hMap⟩ := ih₁ tagged hValues
    obtain ⟨reordered, hSecond, hMap'⟩ := ih₂ middle hMap
    exact ⟨reordered, hFirst.trans hSecond, hMap'⟩

theorem keptRemovedByOrigin : KeptRemovedByOrigin := by
  intro left right kept removed h
  have hValues : (left.map Sum.inl ++ right.map Sum.inr).map forgetOrigin = left ++ right := by
    simp [List.map_map, Function.comp_def, forgetOrigin]
  obtain ⟨tagged, hPerm, hMap⟩ := transportOrigins h _ hValues
  obtain ⟨keptTagged, removedTagged, rfl, hKept, hRemoved⟩ := List.map_eq_append_iff.mp hMap
  exact ⟨keptTagged, removedTagged, hPerm, hKept, hRemoved⟩

end LogicLineages.PersistentMarking.NumberedWindowArithmeticKeptRemovedOriginProof
