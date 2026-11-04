module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovUnaryDecisionTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovUnarySignSemanticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovUnaryDecision.Proof
open SnyatkovUnarySign

private theorem fold_max_le (xs : List Nat) (n : Nat) :
    xs.foldr max 0 ≤ n ↔ ∀ k ∈ xs, k ≤ n := by
  induction xs with
  | nil => simp
  | cons k xs ih => simp only [List.foldr_cons, max_le_iff, ih, List.forall_mem_cons]

private theorem member_le_sum (xs : List Nat) (k : Nat) (hk : k ∈ xs) : k ≤ xs.sum := by
  induction xs with
  | nil => simp at hk
  | cons j xs ih =>
    rcases List.mem_cons.mp hk with h | h
    · subst k
      simp only [List.sum_cons]
      omega
    · have hi := ih h
      simp only [List.sum_cons]
      omega

private theorem domain_exact (M : Matrix) (n : Nat) : matrixDomain M ≤ n ↔
    ∀ C ∈ M, ∀ a ∈ C, ∀ occurrence ∈ a.1.1, 0 ≤ (n : Int) + occurrence.2 := by
  unfold matrixDomain
  rw [fold_max_le]
  constructor
  · intro h C hC a ha
    have hm : a ∈ M.flatten := List.mem_flatten.mpr ⟨C, hC, ha⟩
    have hd := h (domainBound a.1) (List.mem_map.mpr ⟨a, hm, rfl⟩)
    exact (SignedShiftCollection.Proof.domainOffset_le_iff a.1.1 n).mp hd
  · intro h d hd
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
    obtain ⟨C, hC, ha⟩ := List.mem_flatten.mp ha
    exact (SignedShiftCollection.Proof.domainOffset_le_iff a.1.1 n).mpr (h C hC a ha)

private theorem domain_lt_threshold (M : Matrix) : matrixDomain M < matrixThreshold M := by
  unfold matrixThreshold
  omega

private theorem atom_threshold (M : Matrix) (a : Atom) (ha : a ∈ M.flatten) :
    threshold a.1 ≤ matrixThreshold M := by
  have h := member_le_sum ((M.flatten).map (fun a => threshold a.1)) (threshold a.1)
    (List.mem_map.mpr ⟨a, ha, rfl⟩)
  unfold matrixThreshold
  omega

private theorem atom_stable (M : Matrix) (a : Atom) (ha : a ∈ M.flatten)
    (n : Nat) (hn : matrixThreshold M ≤ n) : atomValue a n = tailAtom a := by
  have ht := (SnyatkovUnarySign.Proof.originalDomainAndTailSign a.1).2 n
    ((atom_threshold M a ha).trans hn)
  unfold atomValue tailAtom
  rw [ht.2]

private theorem matrix_stable (M : Matrix) (n : Nat) (hn : matrixThreshold M ≤ n) :
    matrixValue M n = tailValue M := by
  rw [Bool.eq_iff_iff]
  simp only [matrixValue, tailValue, clauseValue, List.any_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, ?_⟩
    intro a ha
    have hs := atom_stable M a (List.mem_flatten.mpr ⟨C, hC, ha⟩) n hn
    simpa only [hs] using h a ha
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, ?_⟩
    intro a ha
    have hs := atom_stable M a (List.mem_flatten.mpr ⟨C, hC, ha⟩) n hn
    simpa only [hs] using h a ha

theorem originalDomainAndMatrixTail : Targets.OriginalDomainAndMatrixTail :=
  fun M => ⟨domain_exact M, domain_lt_threshold M, matrix_stable M⟩

theorem actualExistentialDecision : Targets.ActualExistentialDecision := by
  intro M
  simp only [existsDecision, Bool.or_eq_true, List.any_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, List.mem_range]
  constructor
  · rintro (⟨n, hn, hd, hv⟩ | ht)
    · exact ⟨n, hd, hv⟩
    · refine ⟨matrixThreshold M, (domain_lt_threshold M).le, ?_⟩
      rw [matrix_stable M _ le_rfl]
      exact ht
  · rintro ⟨n, hd, hv⟩
    by_cases hn : n < matrixThreshold M
    · exact Or.inl ⟨n, hn, hd, hv⟩
    · have ht := matrix_stable M n (by omega)
      exact Or.inr (ht ▸ hv)

private theorem finite_forall (M : Matrix) :
    ((List.range (matrixThreshold M)).all (fun n =>
      (!decide (matrixDomain M ≤ n)) || matrixValue M n) = true ↔
      ∀ n : Nat, n < matrixThreshold M → matrixDomain M ≤ n → matrixValue M n = true) := by
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true, decide_eq_false_iff_not]
  constructor
  · intro h n hn hd
    exact (h n hn).resolve_left (by simpa using hd)
  · intro h n hn
    by_cases hd : matrixDomain M ≤ n
    · exact Or.inr (h n hn hd)
    · exact Or.inl (by simp [hd])

theorem actualUniversalDecision : Targets.ActualUniversalDecision := by
  intro M
  simp only [forallDecision, Bool.and_eq_true]
  rw [finite_forall]
  constructor
  · rintro ⟨hs, ht⟩ n hd
    by_cases hn : n < matrixThreshold M
    · exact hs n hn hd
    · rw [matrix_stable M n (by omega)]
      exact ht
  · intro h
    refine ⟨fun n _ hd => h n hd, ?_⟩
    have ht := h (matrixThreshold M) (domain_lt_threshold M).le
    rw [matrix_stable M _ le_rfl] at ht
    exact ht

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovUnaryDecision.Proof
