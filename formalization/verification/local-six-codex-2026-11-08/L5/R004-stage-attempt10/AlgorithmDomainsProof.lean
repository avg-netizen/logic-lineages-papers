module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmSyntaxProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmSignItemProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof
open PolynomialGraphCompletion WordLinearDecisionCompletion Algorithm

/-- Every generated residual domain is paid before evaluating any partition
guard. Inconsistent branches have the same unconditional domain guarantee. -/
theorem classReplacement_domain (D : Nat) (r : Row) (xs : List Item)
    (hDegree : 3 ≤ D) (hD : RowAllowed D r)
    (hxs : ∀ a ∈ xs, a ∈ active (canonicalRow r))
    (ν : Nat → Nat) (ht : ∀ a ∈ xs, sourceTail a ≤ ν a.2.1) :
    RowDomain (classReplacement D xs) ν := by
  by_cases ho : hasOrdinary xs = true
  · simp only [classReplacement,ho,if_true]
    apply foldRows_domain
    intro s hs
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hs
    exact (ordinaryResidual_identity D r a hD (hxs a ha) ν (ht a ha)).2.1
  · have hf : hasOrdinary xs = false := Bool.eq_false_of_not_eq_true ho
    have hc := hasOrdinary_false xs hf
    have href : 3 ≤ leastRank D xs := leastRank_lower D 3 xs (by omega) (by
      intro a ha
      have hp := counter_parameters D r a hD (hxs a ha) (hc a ha)
      omega)
    simp only [classReplacement,hf,Bool.false_eq_true,if_false]
    apply foldRows_domain
    intro s hs
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hs
    exact (counterResidual_allowed_domain D r a hD (hxs a ha) (hc a ha)
      (leastRank D xs) href (leastRank_le_member D xs a ha) ν (ht a ha)).2

theorem rewrite_domain (D : Nat) (r : Row) (labels : List Nat) (removed : Nat)
    (hDegree : 3 ≤ D) (hD : RowAllowed D r) (ν : Nat → Nat) (hd : RowDomain r ν)
    (ht : ∀ a ∈ active (canonicalRow r), sourceTail a ≤ ν a.2.1) :
    RowDomain (rewrite D (canonicalRow r) labels removed) ν := by
  have hcanonical := canonical_domain r ν hd
  have hclass := classReplacement_domain D r _ hDegree hD
    (class_item_current r labels removed) ν
    (fun a ha => ht a (class_item_current r labels removed a ha))
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hcanonical a (outside_subset _ labels removed a ha)
  · exact hclass a ha

theorem stage_branch_tail (D maximum : Nat) (r : Row) (b : Branch)
    (hb : b ∈ stage D maximum r) : b.tail ≤ stageCutoff D maximum r :=
  member_le_foldMax _ _ (List.mem_map.mpr ⟨b,hb,rfl⟩)

theorem region_current (tail maximum : Nat) (r : Row) (ν : Nat → Nat)
    (h : Region tail maximum (rowVariables r) ν) :
    ∀ a ∈ (canonicalRow r).2, tail ≤ ν a.2.1 ∧ ν a.2.1 ≤ ν maximum := by
  intro a ha
  exact h a.2.1 (canonical_names r a.2.1 (List.mem_map.mpr ⟨a,ha,rfl⟩))

theorem partition_branch_member (D maximum : Nat) (r : Row)
    (hm : hasMaximum maximum (canonicalRow r) = true) (labels : List Nat)
    (hl : labels ∈ assignments (active (canonicalRow r)).length (active (canonicalRow r)).length) :
    let out := partitionBranch D maximum (canonicalRow r) labels
    {out with tail := max (rowTail r) out.tail} ∈ stage D maximum r := by
  simp only [stage,hm,if_true]
  exact List.mem_map.mpr ⟨labels,hl,rfl⟩

theorem partitionTail_le_stageCutoff (D maximum : Nat) (r : Row)
    (hm : hasMaximum maximum (canonicalRow r) = true) (labels : List Nat)
    (hl : labels ∈ assignments (active (canonicalRow r)).length (active (canonicalRow r)).length) :
    partitionTail D maximum (canonicalRow r) ≤ stageCutoff D maximum r := by
  have hb := partition_branch_member D maximum r hm labels hl
  have ht := stage_branch_tail D maximum r _ hb
  have hp : partitionTail D maximum (canonicalRow r) ≤
      (partitionBranch D maximum (canonicalRow r) labels).tail := by
    cases hz : zeroClass (canonicalRow r) labels with
    | none => simpa [partitionBranch,hz] using (Nat.le_max_left
        (partitionTail D maximum (canonicalRow r)) (signTail (canonicalRow r)))
    | some removed => simp [partitionBranch,hz]
  exact hp.trans ((Nat.le_max_right _ _).trans ht)

theorem signTail_le_stageCutoff (D maximum : Nat) (r : Row)
    (hm : hasMaximum maximum (canonicalRow r) = true) (labels : List Nat)
    (hl : labels ∈ assignments (active (canonicalRow r)).length (active (canonicalRow r)).length)
    (hz : zeroClass (canonicalRow r) labels = none) :
    signTail (canonicalRow r) ≤ stageCutoff D maximum r := by
  have hb := partition_branch_member D maximum r hm labels hl
  have ht := stage_branch_tail D maximum r _ hb
  have hp : signTail (canonicalRow r) ≤
      (partitionBranch D maximum (canonicalRow r) labels).tail := by
    simpa [partitionBranch,hz] using (Nat.le_max_right
      (partitionTail D maximum (canonicalRow r)) (signTail (canonicalRow r)))
  exact hp.trans ((Nat.le_max_right _ _).trans ht)

theorem stage_nonempty (D maximum : Nat) (r : Row) : stage D maximum r ≠ [] := by
  by_cases hm : hasMaximum maximum (canonicalRow r) = true
  · have hw := witnessLabels_admitted (active (canonicalRow r)) (fun _ => 0)
    have hb := partition_branch_member D maximum r hm _ hw
    intro hn
    simp [hn] at hb
  · simp [stage,hm]

theorem originalTail_le_stageCutoff (D maximum : Nat) (r : Row) :
    rowTail r ≤ stageCutoff D maximum r := by
  obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil _ (stage_nonempty D maximum r)
  have ht : rowTail r ≤ b.tail := by
    by_cases hm : hasMaximum maximum (canonicalRow r) = true
    · obtain ⟨labels,hl,rfl⟩ := List.mem_map.mp (by simpa [stage,hm] using hb)
      exact Nat.le_max_left _ _
    · have he : b = ⟨max (rowTail r) (rowSourceTail (canonicalRow r)),.top,
          .finish ⟨3,canonicalRow r⟩⟩ := by simpa [stage,hm] using hb
      rw [he]
      exact Nat.le_max_left _ _
  exact ht.trans (stage_branch_tail D maximum r b hb)

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof
