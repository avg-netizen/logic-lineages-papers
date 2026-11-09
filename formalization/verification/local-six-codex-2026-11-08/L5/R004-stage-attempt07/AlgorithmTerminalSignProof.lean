module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmSignClassProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof
open PolynomialGraphCompletion WordLinearDecisionCompletion Algorithm

private theorem member_le_sum (xs : List Nat) (a : Nat) (ha : a ∈ xs) : a ≤ xs.sum := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
      rcases List.mem_cons.mp ha with rfl | ha
      · simp
      · have hi := ih ha
        simp only [List.sum_cons]
        omega

private theorem orderNat_respects_le (A B i j : Nat)
    (he : FullWordGuardCompletion.orderNat A B = FullWordGuardCompletion.orderNat i j)
    (hle : i ≤ j) : A ≤ B := by
  unfold FullWordGuardCompletion.orderNat at he
  split_ifs at he <;> omega

/-- The actual final nonempty label class supplies a nonzero collected
coefficient at the greatest actual preimage. Current raw-maximum provenance
and all source correction bounds are derived from current occurrences. -/
theorem terminal_partition_sign (D maximum : Nat) (r : Row) (labels : List Nat)
    (hDegree : 3 ≤ D) (hD : RowAllowed D r)
    (hlabels : labels ∈ assignments (active (canonicalRow r)).length (active (canonicalRow r)).length)
    (hmaximum : hasMaximum maximum (canonicalRow r) = true)
    (hzero : zeroClass (canonicalRow r) labels = none) (ν : Nat → Nat)
    (hpartition : ∀ a ∈ active (canonicalRow r),
      partitionTail D maximum (canonicalRow r) ≤ ν a.2.1 ∧ ν a.2.1 ≤ ν maximum)
    (hsign : ∀ a ∈ active (canonicalRow r), signTail (canonicalRow r) ≤ ν a.2.1)
    (hrawMaximum : ∀ a ∈ (canonicalRow r).2, ν a.2.1 ≤ ν maximum)
    (hg : Formula.eval ν (partitionGuard D maximum (canonicalRow r) labels)) :
    leading ((classes (canonicalRow r) labels).getLastD []) ≠ 0 ∧
      Int.sign (RowValue (canonicalRow r) ν) =
        Int.sign (leading ((classes (canonicalRow r) labels).getLastD [])) := by
  let current := canonicalRow r
  have hl := (assignments_membership _ _ _).mp hlabels
  obtain ⟨maxItem,hmaxItem,hmaxCoeff,hmaxName⟩ := current_maximum_witness maximum r hmaximum
  have hne : active current ≠ [] := by intro hn; simp [hn] at hmaxItem
  obtain ⟨label,hlabel,hclass,hgreatest,hall⟩ := greatest_class_data current labels hl.1 hl.2 hne
  obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil _ hclass
  have hbActive := class_item_current r labels label b hb
  have hbPair := (leaderClass_pair _ _ _).mp hb
  have hcoef := zeroClass_none_nonzero current labels label hzero hlabel hclass
  have hchosen := class_collected_member D maximum r labels hDegree hD hl.1 ν hpartition hg label b hb hcoef
  let U := wordValue (preimage b) (ν b.2.1)
  have hsource : ∀ a ∈ active current, sourceTail a ≤ ν a.2.1 := by
    intro a ha
    exact (rowSourceTail_source current a ha).trans
      ((Nat.le_max_left _ _).trans (hpartition a ha).1)
  have hzip : (labelled current labels).map Prod.fst = active current := List.map_fst_zip (by omega)
  have hU : ∀ a ∈ active current, wordValue (preimage a) (ν a.2.1) ≤ U := by
    intro a ha
    have haMap : a ∈ (labelled current labels).map Prod.fst := by rwa [hzip]
    obtain ⟨p,hp,hpa⟩ := List.mem_map.mp haMap
    subst a
    have horder := (partitionGuard_facts D maximum r labels hDegree hD ν hpartition).2.2.2.mp hg
      p hp (b,label) hbPair
    have hleaderLE := orderNat_respects_le _ _ _ _ horder (hall p hp)
    have haActive := (List.of_mem_zip hp).1
    have hphiA := (preimage_facts D r p.1 hD haActive _ (hsource p.1 haActive)).2.2
    have hphiB := (preimage_facts D r b hD hbActive _ (hsource b hbActive)).2.2
    by_contra hn
    have hu : U < wordValue (preimage p.1) (ν p.1.2.1) := by omega
    have hPhi := Phi_strictMono hu
    change Phi (wordValue (preimage b) (ν b.2.1)) < _ at hPhi
    rw [← hphiA,← hphiB] at hPhi
    omega
  have hmaxProvenance := current_preimage_provenance D r maxItem hD hmaxItem _ (hsign maxItem hmaxItem)
  have hoffset : WordGuardCompletion.wordOffset (preimage maxItem) ≤ preimageOffset current :=
    member_le_sum _ _ (List.mem_map.mpr ⟨maxItem,hmaxItem,rfl⟩)
  have hrawBound : ν maximum ≤ U+preimageOffset current := by
    have hm := hmaxProvenance.2.2.1
    have hu := hU maxItem hmaxItem
    rw [hmaxName] at hm
    omega
  have hraw : ∀ a ∈ linearPart current, ν a.2.1 ≤ U+preimageOffset current := by
    intro a ha
    exact (hrawMaximum a (List.mem_filter.mp ha).1).trans hrawBound
  have hpay : signPayment current ≤ U :=
    (current_preimage_provenance D r b hD hbActive _ (hsign b hbActive)).2.1
  have hs := actual_collected_sign D r hD ν
    (leading (leaderClass (labelled current labels) label),U) hchosen hsource hU hraw hpay
  rw [hgreatest]
  exact ⟨hcoef,hs⟩

theorem terminal_partition_strict (D maximum : Nat) (r : Row) (labels : List Nat)
    (hDegree : 3 ≤ D) (hD : RowAllowed D r)
    (hlabels : labels ∈ assignments (active (canonicalRow r)).length (active (canonicalRow r)).length)
    (hmaximum : hasMaximum maximum (canonicalRow r) = true)
    (hzero : zeroClass (canonicalRow r) labels = none) (ν : Nat → Nat)
    (hpartition : ∀ a ∈ active (canonicalRow r),
      partitionTail D maximum (canonicalRow r) ≤ ν a.2.1 ∧ ν a.2.1 ≤ ν maximum)
    (hsign : ∀ a ∈ active (canonicalRow r), signTail (canonicalRow r) ≤ ν a.2.1)
    (hrawMaximum : ∀ a ∈ (canonicalRow r).2, ν a.2.1 ≤ ν maximum)
    (hg : Formula.eval ν (partitionGuard D maximum (canonicalRow r) labels)) :
    (leading ((classes (canonicalRow r) labels).getLastD []) < 0 →
        RowValue (canonicalRow r) ν < 0) ∧
      (¬leading ((classes (canonicalRow r) labels).getLastD []) < 0 →
        0 < RowValue (canonicalRow r) ν) := by
  have hs := terminal_partition_sign D maximum r labels hDegree hD hlabels hmaximum hzero ν
    hpartition hsign hrawMaximum hg
  constructor
  · intro hneg
    have he : Int.sign (RowValue (canonicalRow r) ν) = -1 := by
      rw [hs.2,Int.sign_eq_neg_one_of_neg hneg]
    exact Int.sign_eq_neg_one_iff_neg.mp he
  · intro hn
    have hnonzero := hs.1
    have hpos : 0 < leading ((classes (canonicalRow r) labels).getLastD []) := by omega
    have he : Int.sign (RowValue (canonicalRow r) ν) = 1 := by
      rw [hs.2,Int.sign_eq_one_of_pos hpos]
    exact Int.sign_eq_one_iff_pos.mp he

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof
