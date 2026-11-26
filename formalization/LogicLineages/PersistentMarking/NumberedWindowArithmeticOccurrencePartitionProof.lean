import LogicLineages.PersistentMarking.NumberedWindowArithmeticKeptRemovedOriginProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectMultisetDomain

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticOccurrencePartitionProof
open NumberedWindowArithmeticAllContextTargets NumberedWindowArithmeticDirectMultisetTargets
open NumberedWindowArithmeticOccurrencePartitionTargets

private def originOf : Sum Nat Nat → Bool := Sum.elim (fun _ => false) (fun _ => true)

private def tagLike (entry : Sum Nat Nat) (value : Nat) : Sum Nat Nat :=
  Sum.elim (fun _ => .inl value) (fun _ => .inr value) entry

private def selectValue (side : Bool) (entry : Sum Nat Nat) : Option Nat :=
  if originOf entry = side then some (forgetOrigin entry) else none

private def part (side : Bool) (entries : List (Sum Nat Nat)) : List Nat :=
  entries.filterMap (selectValue side)

private theorem selectValueSome {side entry value} :
    selectValue side entry = some value ↔ originOf entry = side ∧ forgetOrigin entry = value := by
  by_cases h : originOf entry = side <;> simp [selectValue, h]

private theorem sourceParts (left right : List Nat) (kept removed : List (Sum Nat Nat))
    (h : (left.map Sum.inl ++ right.map Sum.inr).Perm (kept ++ removed)) :
    left.Perm (part false kept ++ part false removed) ∧
      right.Perm (part true kept ++ part true removed) := by
  have noneFilter (xs : List Nat) : xs.filterMap (fun _ => (none : Option Nat)) = [] :=
    List.filterMap_eq_nil_iff.mpr fun _ _ => rfl
  constructor
  · have hLeft := h.filterMap (selectValue false)
    simpa [part, List.filterMap_map, Function.comp_def, selectValue, originOf, forgetOrigin,
      noneFilter] using hLeft
  · have hRight := h.filterMap (selectValue true)
    simpa [part, List.filterMap_map, Function.comp_def, selectValue, originOf, forgetOrigin,
      noneFilter] using hRight

private theorem permParts (entries : List (Sum Nat Nat)) :
    (entries.map forgetOrigin).Perm (part false entries ++ part true entries) := by
  induction entries with
  | nil => exact .nil
  | cons entry rest ih =>
    cases entry with
    | inl value =>
      simpa [part, selectValue, originOf, forgetOrigin] using ih.cons value
    | inr value =>
      have h := (ih.cons value).trans List.perm_middle.symm
      simpa [part, selectValue, originOf, forgetOrigin] using h

/-- Assign each inserted occurrence to the component of one removed dominator.
The same removed occurrence may supply several insertions. -/
private theorem labelInserted {S K} (removed : List (Sum Nat Nat)) (added : List Nat)
    (h : ∀ a ∈ added, ∃ b ∈ removed.map forgetOrigin, AddressPositive S K b a) :
    ∃ tagged : List (Sum Nat Nat), tagged.map forgetOrigin = added ∧
      ∀ entry ∈ tagged, ∃ src ∈ removed, originOf src = originOf entry ∧
        AddressPositive S K (forgetOrigin src) (forgetOrigin entry) := by
  induction added with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons a rest ih =>
    obtain ⟨b, hMem, hDecrease⟩ := h a List.mem_cons_self
    obtain ⟨src, hSrc, rfl⟩ := List.mem_map.mp hMem
    obtain ⟨tagged, hMap, hDominators⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hValue : forgetOrigin (tagLike src a) = a := by cases src <;> rfl
    have hOrigin : originOf src = originOf (tagLike src a) := by cases src <;> rfl
    refine ⟨tagLike src a :: tagged, by simp only [List.map_cons, hValue, hMap], ?_⟩
    intro entry hEntry
    rcases List.mem_cons.mp hEntry with rfl | hTail
    · exact ⟨src, hSrc, hOrigin, by simpa only [hValue] using hDecrease⟩
    · exact hDominators entry hTail

private theorem componentDominators {S K removed added}
    (h : ∀ entry ∈ added, ∃ src ∈ removed, originOf src = originOf entry ∧
      AddressPositive S K (forgetOrigin src) (forgetOrigin entry))
    (side : Bool) :
    ∀ a ∈ part side added, ∃ b ∈ part side removed, AddressPositive S K b a := by
  intro a ha
  obtain ⟨entry, hMem, hSelect⟩ := List.mem_filterMap.mp ha
  obtain ⟨hSide, hValue⟩ := selectValueSome.mp hSelect
  obtain ⟨src, hSrc, hOrigin, hDecrease⟩ := h entry hMem
  exact ⟨forgetOrigin src, List.mem_filterMap.mpr
    ⟨src, hSrc, selectValueSome.mpr ⟨hOrigin.trans hSide, rfl⟩⟩, hValue ▸ hDecrease⟩

private theorem emptyRemoval {S K} {source kept removed added : List Nat}
    (hSource : source.Perm (kept ++ removed))
    (hDom : ∀ a ∈ added, ∃ b ∈ removed, AddressPositive S K b a)
    (hEmpty : removed = []) : source.Perm (kept ++ added) := by
  have hAdded : added = [] := by
    cases added with
    | nil => rfl
    | cons a rest =>
      obtain ⟨b, hMem, _⟩ := hDom a List.mem_cons_self
      rw [hEmpty] at hMem
      cases hMem
  rw [hEmpty] at hSource
  rwa [hAdded]

theorem addressDirectUnionSplit : DirectAddressUnionSplit := by
  intro S K left right target h
  obtain ⟨hTyped, _, kept, removed, added, hSource, hTarget, hNonempty, hDom⟩ := h
  obtain ⟨keptTagged, removedTagged, hTagged, hKept, hRemoved⟩ :=
    NumberedWindowArithmeticKeptRemovedOriginProof.keptRemovedByOrigin left right kept removed hSource
  obtain ⟨pLeft, pRight⟩ := sourceParts left right keptTagged removedTagged hTagged
  rw [← hRemoved] at hDom
  obtain ⟨addedTagged, hAdded, hLabels⟩ := labelInserted removedTagged added hDom
  have pKept : kept.Perm (part false keptTagged ++ part true keptTagged) :=
    hKept ▸ permParts keptTagged
  have pAdded : added.Perm (part false addedTagged ++ part true addedTagged) :=
    hAdded ▸ permParts addedTagged
  have pRegroup :
      ((part false keptTagged ++ part true keptTagged) ++
        (part false addedTagged ++ part true addedTagged)).Perm
      ((part false keptTagged ++ part false addedTagged) ++
        (part true keptTagged ++ part true addedTagged)) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm_assoc (part true keptTagged) (part false addedTagged)
        (part true addedTagged)).append_left (part false keptTagged)
  refine ⟨_, _, hTarget.trans ((pKept.append pAdded).trans pRegroup), ?_⟩
  have strictSide (side : Bool) (xs : List Nat) (hXs : TypedAddressList S K xs)
      (hPerm : xs.Perm (part side keptTagged ++ part side removedTagged))
      (hMore : part side removedTagged ≠ []) :
      AddressDirect S K xs (part side keptTagged ++ part side addedTagged) := by
    have hStrict : StrictAddressReplacement S K xs (part side keptTagged ++ part side addedTagged) :=
      ⟨_, _, _, hPerm, .rfl, hMore, componentDominators hLabels side⟩
    exact ⟨hXs, NumberedWindowArithmeticDirectMultisetDomain.preserved S K _ _ hXs hStrict, hStrict⟩
  have hLeftTyped : TypedAddressList S K left := fun a ha => hTyped a (List.mem_append_left _ ha)
  have hRightTyped : TypedAddressList S K right := fun a ha => hTyped a (List.mem_append_right _ ha)
  by_cases hLeft : part false removedTagged = []
  · have hRight : part true removedTagged ≠ [] := by
      intro hEmpty
      have p := permParts removedTagged
      rw [hRemoved, hLeft, hEmpty] at p
      exact hNonempty p.eq_nil
    exact Or.inr ⟨emptyRemoval pLeft (componentDominators hLabels false) hLeft,
      strictSide true right hRightTyped pRight hRight⟩
  · refine Or.inl ⟨strictSide false left hLeftTyped pLeft hLeft, ?_⟩
    by_cases hRight : part true removedTagged = []
    · exact Or.inl (emptyRemoval pRight (componentDominators hLabels true) hRight)
    · exact Or.inr (strictSide true right hRightTyped pRight hRight)

end LogicLineages.PersistentMarking.NumberedWindowArithmeticOccurrencePartitionProof
