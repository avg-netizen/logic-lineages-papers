module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmSignDataProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmRewriteSemanticProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmGreatestClassProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof
open PolynomialGraphCompletion WordLinearDecisionCompletion Algorithm

theorem partition_preimage_equal_iff (D maximum : Nat) (r : Row) (labels : List Nat)
    (hDegree : 3 ≤ D) (hD : RowAllowed D r) (ν : Nat → Nat)
    (ht : ∀ a ∈ active (canonicalRow r),
      partitionTail D maximum (canonicalRow r) ≤ ν a.2.1 ∧ ν a.2.1 ≤ ν maximum)
    (hg : Formula.eval ν (partitionGuard D maximum (canonicalRow r) labels))
    (a b : Labelled) (ha : a ∈ labelled (canonicalRow r) labels)
    (hb : b ∈ labelled (canonicalRow r) labels) :
    wordValue (preimage a.1) (ν a.1.2.1) = wordValue (preimage b.1) (ν b.1.2.1) ↔ a.2 = b.2 := by
  have ha' := (List.of_mem_zip ha).1
  have hb' := (List.of_mem_zip hb).1
  have hta := (rowSourceTail_source _ a.1 ha').trans ((Nat.le_max_left _ _).trans (ht a.1 ha').1)
  have htb := (rowSourceTail_source _ b.1 hb').trans ((Nat.le_max_left _ _).trans (ht b.1 hb').1)
  have hphiA := (preimage_facts D r a.1 hD ha' _ hta).2.2
  have hphiB := (preimage_facts D r b.1 hD hb' _ htb).2.2
  have he := (partitionGuard_facts D maximum r labels hDegree hD ν ht).2.2.2.mp hg a ha b hb
  have hvalues : wordValue (preimage a.1) (ν a.1.2.1) =
      wordValue (preimage b.1) (ν b.1.2.1) ↔
      wordValue (leader a.1).2 (ν a.1.2.1) = wordValue (leader b.1).2 (ν b.1.2.1) := by
    rw [hphiA,hphiB]
    exact Phi_strictMono.injective.eq_iff.symm
  calc
    _ ↔ wordValue (leader a.1).2 (ν a.1.2.1) =
        wordValue (leader b.1).2 (ν b.1.2.1) := hvalues
    _ ↔ FullWordGuardCompletion.orderNat
        (wordValue (leader a.1).2 (ν a.1.2.1))
        (wordValue (leader b.1).2 (ν b.1.2.1)) = 1 := (orderNat_equal_iff _ _).symm
    _ ↔ FullWordGuardCompletion.orderNat a.2 b.2 = 1 := by rw [he]
    _ ↔ a.2 = b.2 := orderNat_equal_iff _ _

private theorem sum_filter_indicator {α : Type} (xs : List α) (p : α → Bool) (f : α → Int) :
    ((xs.filter p).map f).sum = (xs.map (fun a => if p a then f a else 0)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => cases hp : p a <;> simp [hp,ih]

/-- The stage's actual doubled class coefficient agrees with the checked
semantic collection coefficient at its original reached preimage. This
collection is used only in the proof of a terminal sign. -/
theorem class_coefficient_calibration (D maximum : Nat) (r : Row) (labels : List Nat)
    (hDegree : 3 ≤ D) (hD : RowAllowed D r)
    (hlen : labels.length = (active (canonicalRow r)).length) (ν : Nat → Nat)
    (ht : ∀ a ∈ active (canonicalRow r),
      partitionTail D maximum (canonicalRow r) ≤ ν a.2.1 ∧ ν a.2.1 ≤ ν maximum)
    (hg : Formula.eval ν (partitionGuard D maximum (canonicalRow r) labels))
    (label : Nat) (b : Item) (hb : b ∈ leaderClass (labelled (canonicalRow r) labels) label) :
    CommonHeadCollectedRow.coefficient (numericLeaderData (canonicalRow r) ν)
      (wordValue (preimage b) (ν b.2.1)) =
        leading (leaderClass (labelled (canonicalRow r) labels) label) := by
  let zs := labelled (canonicalRow r) labels
  have hzip : zs.map Prod.fst = active (canonicalRow r) := List.map_fst_zip (by omega)
  have hb' : (b,label) ∈ zs := (leaderClass_pair _ _ _).mp hb
  have hpred : ∀ p ∈ zs, wordValue (preimage p.1) (ν p.1.2.1) =
      wordValue (preimage b) (ν b.2.1) ↔ p.2 = label := by
    intro p hp
    exact partition_preimage_equal_iff D maximum r labels hDegree hD ν ht hg p (b,label) hp hb'
  unfold CommonHeadCollectedRow.coefficient numericLeaderData
  simp only [List.map_map,Function.comp_def]
  rw [← hzip]
  simp only [List.map_map,Function.comp_def]
  have hif : (zs.map (fun p => if wordValue (preimage p.1) (ν p.1.2.1) =
        wordValue (preimage b) (ν b.2.1) then p.1.1*(if isCounter p.1 then 1 else 2) else 0)).sum =
      (zs.map (fun p => if p.2 == label then p.1.1*(if isCounter p.1 then 1 else 2) else 0)).sum := by
    congr 1
    apply List.map_congr_left
    intro p hp
    by_cases he : p.2 = label <;> simp [hpred p hp,he]
  rw [hif,← sum_filter_indicator]
  simp only [leading,leaderClass,List.map_map,Function.comp_def]

theorem class_collected_member (D maximum : Nat) (r : Row) (labels : List Nat)
    (hDegree : 3 ≤ D) (hD : RowAllowed D r)
    (hlen : labels.length = (active (canonicalRow r)).length) (ν : Nat → Nat)
    (ht : ∀ a ∈ active (canonicalRow r),
      partitionTail D maximum (canonicalRow r) ≤ ν a.2.1 ∧ ν a.2.1 ≤ ν maximum)
    (hg : Formula.eval ν (partitionGuard D maximum (canonicalRow r) labels))
    (label : Nat) (b : Item) (hb : b ∈ leaderClass (labelled (canonicalRow r) labels) label)
    (hcoef : leading (leaderClass (labelled (canonicalRow r) labels) label) ≠ 0) :
    (leading (leaderClass (labelled (canonicalRow r) labels) label),
      wordValue (preimage b) (ν b.2.1)) ∈
        CommonHeadCollectedRow.collect (numericLeaderData (canonicalRow r) ν) := by
  have hcoeff := class_coefficient_calibration D maximum r labels hDegree hD hlen ν ht hg label b hb
  have hactive := class_item_current r labels label b hb
  have hk : wordValue (preimage b) (ν b.2.1) ∈
      CommonHeadCollectedRow.keys (numericLeaderData (canonicalRow r) ν) := by
    simp only [CommonHeadCollectedRow.keys,List.mem_dedup]
    exact List.mem_map.mpr ⟨(b.1*(if isCounter b then 1 else 2),
      wordValue (preimage b) (ν b.2.1)),List.mem_map.mpr ⟨b,hactive,rfl⟩,rfl⟩
  unfold CommonHeadCollectedRow.collect
  rw [← hcoeff]
  exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨_,hk,rfl⟩,by simpa [hcoeff] using hcoef⟩

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof
