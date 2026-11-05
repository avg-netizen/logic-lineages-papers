module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiRowsPartitionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiRowsProof
open NormalForm InactivePhiRows

private def selected (ν : Nat → Nat) (p : Nat → Bool) : Summand → Bool
  | .phi j e => p (PlainPhiDominance.argument ν j e)
  | _ => false

private def touches (r : Row) (i : Nat) (ν : Nat → Nat) (t : Nat) : Bool :=
  r.2.any (fun a => match a.2 with
    | .phi j e => j == i && PlainPhiDominance.argument ν j e == t
    | _ => false)

private theorem touched_self (r : Row) (i : Nat) (ν : Nat → Nat) (w e : Int)
    (ha : (w, Summand.phi i e) ∈ r.2) :
    touches r i ν (PlainPhiDominance.argument ν i e) = true := by
  apply List.any_eq_true.mpr
  exact ⟨(w, .phi i e), ha, by simp⟩

private theorem touched_coefficient_zero (r : Row) (i : Nat) (ν : Nat → Nat)
    (hi : PlainPhiDominance.active i r ν = false) (t : Nat) (ht : touches r i ν t = true) :
    CommonHeadCollectedRow.coefficient (PlainPhiDominance.phiData r ν) t = 0 := by
  obtain ⟨a, ha, hh⟩ := List.any_eq_true.mp ht
  rcases a with ⟨w, s⟩
  cases s with
  | «variable» j => simp [touches] at hh
  | hyperPhi j e f => simp [touches] at hh
  | phi j e =>
      have hs := Bool.and_eq_true_iff.mp hh
      have hj : j = i := by simpa using hs.1
      have he : PlainPhiDominance.argument ν j e = t := by simpa using hs.2
      subst j
      rw [← he]
      have hz := List.any_eq_false.mp hi (w, .phi i e) ha
      simpa using hz

private theorem dropped_marked (xs : List (Int × Summand)) (p : Int × Summand → Bool) :
    droppedItems (xs.map p) xs = xs.filter p := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      cases hp : p a <;> simp [droppedItems, hp] at ih ⊢ <;> exact ih

private theorem kept_marked (xs : List (Int × Summand)) (p : Int × Summand → Bool) :
    keptItems (xs.map p) xs = xs.filter (fun a => !p a) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      cases hp : p a <;> simp [keptItems, hp] at ih ⊢ <;> exact ih

private theorem selected_phiData (xs : List (Int × Summand)) (ν : Nat → Nat) (p : Nat → Bool) :
    PlainPhiDominance.phiData (0, xs.filter (fun a => selected ν p a.2)) ν =
      (PlainPhiDominance.phiData (0, xs) ν).filter (fun a => p a.2) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      rcases a with ⟨w, s⟩
      cases s with
      | «variable» j => simpa [selected, PlainPhiDominance.phiData] using ih
      | hyperPhi j e f => simpa [selected, PlainPhiDominance.phiData] using ih
      | phi j e =>
          cases hp : p (PlainPhiDominance.argument ν j e) <;>
            simp [selected, PlainPhiDominance.phiData, hp] at ih ⊢ <;> exact ih

private theorem coefficient_filter (row : CommonHeadLargeRow.Row) (p : Nat → Bool) (t : Nat) :
    CommonHeadCollectedRow.coefficient (row.filter (fun a => p a.2)) t =
      if p t then CommonHeadCollectedRow.coefficient row t else 0 := by
  induction row with
  | nil => cases p t <;> simp [CommonHeadCollectedRow.coefficient]
  | cons a row ih =>
      by_cases he : a.2 = t
      · cases hp : p t <;> simp [CommonHeadCollectedRow.coefficient, he, hp] at ih ⊢ <;> exact ih
      · cases ha : p a.2 <;> cases ht : p t <;>
          simp [CommonHeadCollectedRow.coefficient, he, ha, ht] at ih ⊢ <;> exact ih

private theorem marked_onlyPhi (xs : List (Int × Summand)) (ν : Nat → Nat) (p : Nat → Bool) :
    onlyPhi (0, xs.filter (fun a => selected ν p a.2)) = true := by
  apply List.all_eq_true.mpr
  intro a ha
  have hh := (List.mem_filter.mp ha).2
  rcases a with ⟨w, s⟩
  cases s <;> simp_all [selected, onlyPhi]

private theorem marked_remaining_linear (r : Row) (hp : PlainPhiDominance.isPlain r = true)
    (i : Nat) (ν : Nat → Nat) :
    LinearRows.rowLinear i
      (r.1, r.2.filter (fun a => !selected ν (touches r i ν) a.2)) = true := by
  apply List.all_eq_true.mpr
  intro a ha
  have hm := List.mem_filter.mp ha
  have hs := List.all_eq_true.mp hp a hm.1
  rcases a with ⟨w, s⟩
  cases s with
  | «variable» j => rfl
  | hyperPhi j e f => simp [PlainPhiDominance.isPlain] at hs
  | phi j e =>
      by_cases hj : j = i
      · subst j
        have ht := touched_self r i ν w e hm.1
        simp [selected, ht] at hm
      · simpa [LinearRows.summandLinear] using hj

private theorem masks_mem (n : Nat) (mask : List Bool) :
    mask ∈ CommonHeadLargeGuards.masks n ↔ mask.length = n := by
  induction n generalizing mask with
  | zero => cases mask <;> simp [CommonHeadLargeGuards.masks]
  | succ n ih =>
      cases mask with
      | nil => simp [CommonHeadLargeGuards.masks]
      | cons b bs => cases b <;> simp [CommonHeadLargeGuards.masks, ih]

theorem finiteInactiveCoverage : InactivePhiRowsTargets.FiniteInactiveCoverage := by
  intro r hp i ν hi
  let mark : Int × Summand → Bool := fun a => selected ν (touches r i ν) a.2
  let mask := r.2.map mark
  have hlen : mask.length = r.2.length := by simp only [mask, List.length_map]
  have hdrop : dropped r mask = (0, r.2.filter mark) := by
    unfold dropped mask
    rw [dropped_marked]
  have hkeep : remaining r mask = (r.1, r.2.filter (fun a => !mark a)) := by
    unfold remaining mask
    rw [kept_marked]
  have had : admissible i r mask = true := by
    have hd := marked_onlyPhi r.2 ν (touches r i ν)
    have hk := marked_remaining_linear r hp i ν
    simp only [admissible, hlen, beq_self_eq_true, Bool.true_and, hdrop, hkeep]
    exact Bool.and_eq_true_iff.mpr ⟨hd, hk⟩
  refine ⟨mask, List.mem_filter.mpr ⟨(masks_mem _ _).mpr hlen, had⟩, ?_⟩
  apply (ShiftedInputGuardsProof.actualCancellationGuard (dropped r mask) ν).mpr
  have hphi : PlainPhiDominance.phiData (dropped r mask) ν =
      (PlainPhiDominance.phiData r ν).filter (fun a => touches r i ν a.2) := by
    rw [hdrop]
    exact selected_phiData r.2 ν (touches r i ν)
  have hz (t : Nat) : CommonHeadCollectedRow.coefficient
      (PlainPhiDominance.phiData (dropped r mask) ν) t = 0 := by
    rw [hphi, coefficient_filter]
    by_cases ht : touches r i ν t = true
    · rw [if_pos ht]
      exact touched_coefficient_zero r i ν hi t ht
    · rw [if_neg ht]
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro a ha
  have hs := (CommonHeadCollectedRow.Proof.literalCollectedSupport
    (PlainPhiDominance.phiData (dropped r mask) ν)).2.1 a ha
  apply hs.1
  rw [hs.2.1, hz]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiRowsProof
