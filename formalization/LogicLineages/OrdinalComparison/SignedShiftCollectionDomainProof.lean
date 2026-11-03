module
public import LogicLineages.OrdinalComparison.SignedShiftCollectionTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.SignedShiftCollection.Proof

/-- The fold starts at an explicit lower bound and visits every list entry. -/
theorem foldlMax_le_iff (xs : List Nat) (m d : Nat) :
    xs.foldl max m ≤ d ↔ m ≤ d ∧ ∀ x ∈ xs, x ≤ d := by
  induction xs generalizing m with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    constructor
    · rintro ⟨hm, ht⟩
      obtain ⟨hm, hx⟩ := max_le_iff.mp hm
      refine ⟨hm, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with he | hy
      · subst y
        exact hx
      · exact ht y hy
    · rintro ⟨hm, ht⟩
      refine ⟨max_le hm (ht x List.mem_cons_self), ?_⟩
      intro y hy
      exact ht y (List.mem_cons_of_mem x hy)

/-- In particular, a zero coefficient or a subsequently cancelled block still
contributes its original signed shift to the least safe offset. -/
theorem domainOffset_le_iff (row : Row) (d : Nat) :
    domainOffset row ≤ d ↔ ∀ a ∈ row, 0 ≤ (d : Int) + a.2 := by
  unfold domainOffset
  rw [foldlMax_le_iff]
  simp only [Nat.zero_le, true_and]
  constructor
  · intro h a ha
    have hb := h (-a.2).toNat (List.mem_map.mpr ⟨a, ha, rfl⟩)
    omega
  · intro h n hn
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hn
    have hb := h a ha
    omega

theorem domainSafe (row : Row) (a : Int × Int) (ha : a ∈ row) :
    0 ≤ (domainOffset row : Int) + a.2 :=
  (domainOffset_le_iff row (domainOffset row)).mp le_rfl a ha

theorem rebaseKey_cast (row : Row) (a : Int × Int) (ha : a ∈ row) :
    (rebaseKey row a.2 : Int) = (domainOffset row : Int) + a.2 := by
  exact Int.toNat_of_nonneg (domainSafe row a ha)

theorem originalShift_rebaseKey (row : Row) (a : Int × Int) (ha : a ∈ row) :
    originalShift row (rebaseKey row a.2) = a.2 := by
  unfold originalShift
  rw [rebaseKey_cast row a ha]
  omega

/-- Unlike injectivity of the total rebasing map, this inverse law is global. -/
theorem rebaseKey_originalShift (row : Row) (k : Nat) :
    rebaseKey row (originalShift row k) = k := by
  unfold rebaseKey originalShift
  have he : (domainOffset row : Int) + ((k : Int) - (domainOffset row : Int)) =
      (k : Int) := by omega
  rw [he]
  simp

theorem rebaseKey_eq_iff_originalShift (row : Row) (a : Int × Int)
    (ha : a ∈ row) (k : Nat) :
    rebaseKey row a.2 = k ↔ a.2 = originalShift row k := by
  constructor
  · intro h
    rw [← h, originalShift_rebaseKey row a ha]
  · intro h
    rw [h, rebaseKey_originalShift]

theorem originalDomainAndRebasing : Targets.OriginalDomainAndRebasing := by
  intro row
  refine ⟨domainOffset_le_iff row, ?_, ?_⟩
  · intro a ha x
    have hs := domainSafe row a ha
    have hk := rebaseKey_cast row a ha
    refine ⟨by omega, ?_, originalShift_rebaseKey row a ha⟩
    omega
  · intro a ha b hb
    have ha' := rebaseKey_cast row a ha
    have hb' := rebaseKey_cast row b hb
    exact ⟨by omega, by omega, by omega⟩

end LogicLineages.OrdinalComparison.SignedShiftCollection.Proof
