module
public import LogicLineages.OrdinalComparison.SignedShiftCollectionDomainProof
public import LogicLineages.OrdinalComparison.CommonHeadCollectedRowAlgebraProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SignedShiftCollection.Proof

/-- The natural-key collector computes the literal signed block sum, including
at keys not represented in the original row (where both sides are zero). -/
theorem coefficient_rebaseRow (row : Row) (k : Nat) :
    CommonHeadCollectedRow.coefficient (rebaseRow row) k =
      coefficient row (originalShift row k) := by
  unfold CommonHeadCollectedRow.coefficient rebaseRow coefficient
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  have hi := rebaseKey_eq_iff_originalShift row a ha k
  by_cases hk : rebaseKey row a.2 = k
  · have hb := hi.mp hk
    simp only [if_pos hk, if_pos hb]
  · have hb : a.2 ≠ originalShift row k := fun hb => hk (hi.mpr hb)
    simp only [if_neg hk, if_neg hb]

theorem coefficient_eq_zero_of_no_occurrence (row : Row) (b : Int)
    (h : ∀ a ∈ row, a.2 ≠ b) : coefficient row b = 0 := by
  induction row with
  | nil => simp [coefficient]
  | cons a row ih =>
    change (if a.2 = b then a.1 else 0) + coefficient row b = 0
    rw [if_neg (h a List.mem_cons_self),
      ih (fun c hc => h c (List.mem_cons_of_mem a hc))]
    rfl

theorem exists_original_of_coefficient_ne_zero (row : Row) (b : Int)
    (h : coefficient row b ≠ 0) : ∃ a ∈ row, a.2 = b := by
  classical
  by_contra hn
  apply h
  apply coefficient_eq_zero_of_no_occurrence
  intro a ha he
  exact hn ⟨a, ha, he⟩

theorem collected_member_data (row : Row) (a : Int × Nat) (ha : a ∈ collected row) :
    a.1 ≠ 0 ∧ a.1 = coefficient row (originalShift row a.2) ∧
      ∃ b ∈ row, b.2 = originalShift row a.2 ∧ rebaseKey row b.2 = a.2 := by
  obtain ⟨hne, hcoef, b, hb, hkey⟩ :=
    (CommonHeadCollectedRow.Proof.literalCollectedSupport (rebaseRow row)).2.1 a ha
  obtain ⟨c, hc, he⟩ := List.mem_map.mp hb
  subst b
  refine ⟨hne, hcoef.trans (coefficient_rebaseRow row a.2), c, hc, ?_, hkey⟩
  exact (rebaseKey_eq_iff_originalShift row c hc a.2).mp hkey

/-- A surviving pair is exactly its nonzero signed block coefficient. Its
original-occurrence provenance follows from the literal nonzero block sum. -/
theorem mem_collected_iff (row : Row) (a : Int × Nat) :
    a ∈ collected row ↔
      a.1 = coefficient row (originalShift row a.2) ∧ a.1 ≠ 0 := by
  constructor
  · intro ha
    have h := collected_member_data row a ha
    exact ⟨h.2.1, h.1⟩
  · rintro ⟨hcoef, hne⟩
    have hnon : coefficient row (originalShift row a.2) ≠ 0 := by
      rw [← hcoef]
      exact hne
    obtain ⟨b, hb, hshift⟩ :=
      exists_original_of_coefficient_ne_zero row (originalShift row a.2) hnon
    have hkey := (rebaseKey_eq_iff_originalShift row b hb a.2).mpr hshift
    change a ∈ CommonHeadCollectedRow.collect (rebaseRow row)
    apply List.mem_filter.mpr
    refine ⟨?_, by simpa using hne⟩
    apply List.mem_map.mpr
    refine ⟨a.2, ?_, ?_⟩
    · simp only [CommonHeadCollectedRow.keys, List.mem_dedup]
      apply List.mem_map.mpr
      refine ⟨(b.1, rebaseKey row b.2), ?_, hkey⟩
      exact List.mem_map.mpr ⟨b, hb, rfl⟩
    · apply Prod.ext
      · exact (coefficient_rebaseRow row a.2).trans hcoef.symm
      · rfl

theorem coefficient_ne_zero_iff (row : Row) (b : Int) :
    coefficient row b ≠ 0 ↔ ∃ a ∈ collected row, originalShift row a.2 = b := by
  constructor
  · intro h
    obtain ⟨c, hc, he⟩ := exists_original_of_coefficient_ne_zero row b h
    have hinv : originalShift row (rebaseKey row b) = b := by
      rw [← he]
      exact originalShift_rebaseKey row c hc
    refine ⟨(coefficient row b, rebaseKey row b), ?_, hinv⟩
    apply (mem_collected_iff row _).mpr
    exact ⟨by simpa only [hinv], h⟩
  · rintro ⟨a, ha, he⟩
    obtain ⟨hcoef, hne⟩ := (mem_collected_iff row a).mp ha
    rw [← he, ← hcoef]
    exact hne

theorem collected_eq_nil_iff (row : Row) :
    collected row = [] ↔ ∀ b : Int, coefficient row b = 0 := by
  constructor
  · intro he b
    by_contra hb
    obtain ⟨a, ha, _⟩ := (coefficient_ne_zero_iff row b).mp hb
    simpa only [he, List.not_mem_nil] using ha
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro a ha
    obtain ⟨hcoef, hne⟩ := (mem_collected_iff row a).mp ha
    exact hne (hcoef.trans (h (originalShift row a.2)))

theorem weighted_collected (row : Row) (f : Int → Int) :
    CommonHeadCollectedRow.weighted (fun k => f (originalShift row k)) (collected row) =
      weighted f row := by
  change CommonHeadCollectedRow.weighted (fun k => f (originalShift row k))
    (CommonHeadCollectedRow.collect (rebaseRow row)) = weighted f row
  rw [CommonHeadCollectedRow.Proof.exactWeightedCollection]
  unfold CommonHeadCollectedRow.weighted rebaseRow weighted
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  rw [originalShift_rebaseKey row a ha]

theorem natural_weighted_collected (row : Row) (f : Nat → Int) (x : Nat) :
    CommonHeadCollectedRow.weighted (fun k => f (x + k)) (collected row) =
      weighted (fun b => f (((x : Int) + (domainOffset row : Int) + b).toNat)) row := by
  change CommonHeadCollectedRow.weighted (fun k => f (x + k))
    (CommonHeadCollectedRow.collect (rebaseRow row)) = _
  rw [CommonHeadCollectedRow.Proof.exactWeightedCollection]
  unfold CommonHeadCollectedRow.weighted rebaseRow weighted
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  have hk := rebaseKey_cast row a ha
  have he : ((x : Int) + (domainOffset row : Int) + a.2).toNat =
      x + rebaseKey row a.2 := by omega
  rw [he]

theorem exactCollectionAndSupport : Targets.ExactCollectionAndSupport := by
  intro row
  have h := CommonHeadCollectedRow.Proof.literalCollectedSupport (rebaseRow row)
  refine ⟨weighted_collected row, natural_weighted_collected row, h.1,
    collected_member_data row, coefficient_ne_zero_iff row, collected_eq_nil_iff row, ?_⟩
  simpa only [collected, CommonHeadLargeRow.mass, rebaseRow,
    List.map_map, Function.comp_def] using h.2.2

end LogicLineages.OrdinalComparison.SignedShiftCollection.Proof
