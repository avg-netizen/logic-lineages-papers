module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmClassSemanticProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmPartitionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof
open PolynomialGraphCompletion WordLinearDecisionCompletion Algorithm

theorem class_member_iff (zs : List Labelled) (removed : Nat) (a : Item) :
    a ∈ leaderClass zs removed ↔ (a,removed) ∈ zs := by
  constructor
  · intro ha
    obtain ⟨b,hb,hba⟩ := List.mem_map.mp ha
    have hc := List.mem_filter.mp hb
    have hlabel : b.2 = removed := by simpa using hc.2
    cases b with
    | mk b label =>
        simp only [Prod.fst,Prod.snd] at hba hlabel
        subst b
        subst label
        exact hc.1
  · intro ha
    exact List.mem_map.mpr ⟨(a,removed),List.mem_filter.mpr ⟨ha,by simp⟩,rfl⟩

theorem orderNat_equal_iff (a b : Nat) :
    FullWordGuardCompletion.orderNat a b = 1 ↔ a = b := by
  by_cases hlt : a < b
  · have hne : a ≠ b := Nat.ne_of_lt hlt
    simp [FullWordGuardCompletion.orderNat,hlt,hne]
  · by_cases heq : a = b <;> simp [FullWordGuardCompletion.orderNat,hlt,heq]

theorem true_partition_same_class (D maximum : Nat) (r : Row) (labels : List Nat)
    (hDegree : 3 ≤ D) (hD : RowAllowed D r) (ν : Nat → Nat)
    (ht : ∀ a ∈ active (canonicalRow r),
      partitionTail D maximum (canonicalRow r) ≤ ν a.2.1 ∧ ν a.2.1 ≤ ν maximum)
    (hg : Formula.eval ν (partitionGuard D maximum (canonicalRow r) labels))
    (removed : Nat) (a b : Item)
    (ha : a ∈ leaderClass (labelled (canonicalRow r) labels) removed)
    (hb : b ∈ leaderClass (labelled (canonicalRow r) labels) removed) :
    wordValue (leader a).2 (ν a.2.1) = wordValue (leader b).2 (ν b.2.1) := by
  have he := (partitionGuard_facts D maximum r labels hDegree hD ν ht).2.2.2.mp hg
    (a,removed) ((class_member_iff _ _ _).mp ha)
    (b,removed) ((class_member_iff _ _ _).mp hb)
  apply (orderNat_equal_iff _ _).mp
  simpa [FullWordGuardCompletion.orderNat] using he

theorem rowSourceTail_collision (r : Row) (a b : Item)
    (ha : a ∈ active r) (hb : b ∈ active r) : collisionTail a b ≤ rowSourceTail r := by
  apply (member_le_foldMax _ _ ?_).trans
    ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  exact List.mem_flatMap.mpr ⟨a,ha,List.mem_map.mpr ⟨b,hb,rfl⟩⟩

theorem rewrite_value_from_class (D : Nat) (r : Row) (labels : List Nat) (removed : Nat)
    (hlen : labels.length = (active r).length) (ν : Nat → Nat)
    (he : RowValue (classReplacement D (leaderClass (labelled r labels) removed)) ν =
      ((leaderClass (labelled r labels) removed).map
        (fun a => a.1*(wordValue a.2.2 (ν a.2.1) : Int))).sum) :
    RowValue (rewrite D r labels removed) ν = RowValue r ν := by
  have hp := ((partition_items_permutation r labels removed hlen).map
    (fun a => a.1*(wordValue a.2.2 (ν a.2.1) : Int))).sum_eq
  simp only [List.map_append,List.sum_append] at hp
  simp only [RowValue] at he
  simp only [rewrite,RowValue,List.map_append,List.sum_append]
  linear_combination hp+he

/-- Exact semantic cancellation for the actual removed class selected by the
finite stage. Domains of every emitted residual are supplied before asking
whether the partition guard is true. -/
theorem actual_zero_class_identity (D maximum : Nat) (r : Row) (labels : List Nat)
    (hDegree : 3 ≤ D) (hD : RowAllowed D r)
    (hlen : labels.length = (active (canonicalRow r)).length) (removed : Nat)
    (hne : leaderClass (labelled (canonicalRow r) labels) removed ≠ [])
    (hz : leading (leaderClass (labelled (canonicalRow r) labels) removed) = 0)
    (ν : Nat → Nat)
    (ht : ∀ a ∈ active (canonicalRow r),
      partitionTail D maximum (canonicalRow r) ≤ ν a.2.1 ∧ ν a.2.1 ≤ ν maximum)
    (hg : Formula.eval ν (partitionGuard D maximum (canonicalRow r) labels)) :
    RowValue (rewrite D (canonicalRow r) labels removed) ν = RowValue (canonicalRow r) ν := by
  let xs := leaderClass (labelled (canonicalRow r) labels) removed
  have hxs : ∀ a ∈ xs, a ∈ active (canonicalRow r) := class_item_current r labels removed
  have htail : ∀ a ∈ xs, sourceTail a ≤ ν a.2.1 := by
    intro a ha
    have hs : sourceTail a ≤ rowSourceTail (canonicalRow r) :=
      (member_le_foldMax _ _ (List.mem_map.mpr ⟨a,hxs a ha,rfl⟩)).trans
        ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
    exact hs.trans
      ((Nat.le_max_left _ _).trans (ht a (hxs a ha)).1)
  have hpairs : ∀ a ∈ xs, ∀ b ∈ xs,
      collisionTail a b ≤ ν a.2.1 ∧ collisionTail a b ≤ ν b.2.1 := by
    intro a ha b hb
    have hp := (rowSourceTail_collision _ a b (hxs a ha) (hxs b hb)).trans
      (Nat.le_max_left _ _ : rowSourceTail (canonicalRow r) ≤
        partitionTail D maximum (canonicalRow r))
    exact ⟨hp.trans (ht a (hxs a ha)).1,hp.trans (ht b (hxs b hb)).1⟩
  have hsame : ∀ a ∈ xs, ∀ b ∈ xs,
      wordValue (leader a).2 (ν a.2.1) = wordValue (leader b).2 (ν b.2.1) :=
    fun a ha b hb => true_partition_same_class D maximum r labels hDegree hD ν ht hg removed a b ha hb
  apply rewrite_value_from_class D (canonicalRow r) labels removed hlen ν
  by_cases ho : hasOrdinary xs = true
  · obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil xs hne
    exact (ordinaryClass_identity D r xs hD hxs ho hz ν htail
      (wordValue (leader b).2 (ν b.2.1)) (fun a ha => hsame a ha b hb)).2.2
  · exact (counterClass_identity D r xs hD hxs (Bool.eq_false_of_not_eq_true ho)
      hne hz ν htail hpairs hsame).2.2

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof
