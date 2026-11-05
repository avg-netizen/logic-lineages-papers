module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainPhiDominanceTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowProof
public import LogicLineages.OrdinalComparison.CommonHeadCollectedRowAlgebraProof

public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainPhiDominanceProof
open NormalForm PlainPhiDominance

private theorem raw_evaluation (z : Int) (xs : List (Int × Summand)) (ν : Nat → Nat)
    (h : isPlain (z, xs) = true) :
    rowValue (z, xs) ν = linearPart (z, xs) ν +
      CommonHeadCollectedRow.weighted (fun n => (Phi n : Int)) (phiData (z, xs) ν) := by
  induction xs with
  | nil => simp [rowValue, linearPart, phiData, CommonHeadCollectedRow.weighted]
  | cons a xs ih =>
      have hh := Bool.and_eq_true_iff.mp h
      have hi := ih hh.2
      rcases a with ⟨w, s⟩
      cases s with
      | «variable» i =>
          simp only [rowValue, linearPart, phiData, List.map_cons, List.sum_cons,
            List.flatMap_cons, List.nil_append, Summand.term, Term.value] at hi ⊢
          omega
      | phi i e =>
          simp only [rowValue, linearPart, phiData, List.map_cons, List.sum_cons,
            List.flatMap_cons, List.singleton_append, Summand.term, Term.value,
            WindowProof.shifted_value, CommonHeadCollectedRow.weighted, argument] at hi ⊢
          omega
      | hyperPhi i e f =>
          simp [isPlain] at hh

theorem phiData_mass (r : Row) (ν : Nat → Nat) :
    CommonHeadLargeRow.mass (phiData r ν) ≤ mass r := by
  rcases r with ⟨z, xs⟩
  induction xs with
  | nil => simp [phiData, mass, CommonHeadLargeRow.mass]
  | cons a xs ih =>
      rcases a with ⟨w, s⟩
      cases s <;> simp only [phiData, mass, CommonHeadLargeRow.mass,
        List.flatMap_cons, List.map_cons, List.sum_cons, List.nil_append,
        List.singleton_append] at ih ⊢ <;> omega

theorem exactCollectedEvaluation : PlainPhiDominanceTargets.ExactCollectedEvaluation := by
  intro r h ν
  refine ⟨?_, (CommonHeadCollectedRow.Proof.literalCollectedSupport (phiData r ν)).2.2.trans
    (phiData_mass r ν)⟩
  rw [CommonHeadCollectedRow.Proof.exactWeightedCollection]
  exact raw_evaluation r.1 r.2 ν h

theorem actualCancelledRow : PlainPhiDominanceTargets.ActualCancelledRow := by
  intro r h ν hc
  have he := (exactCollectedEvaluation r h ν).1
  simpa [hc, CommonHeadCollectedRow.weighted] using he

private theorem linear_sum_bound (xs : List (Int × Summand)) (ν : Nat → Nat) (X : Nat)
    (h : ∀ a ∈ xs, ν a.2.name ≤ X) :
    ((xs.map (fun a : Int × Summand => match a.2 with
      | .variable i => a.1 * (ν i : Int)
      | _ => 0)).sum).natAbs ≤ (xs.map (fun a => a.1.natAbs)).sum * X := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha := h a List.mem_cons_self
      have ht := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
      rcases a with ⟨w, s⟩
      cases s with
      | «variable» i =>
          have hadd := Int.natAbs_add_le (w * (ν i : Int))
            ((xs.map (fun a : Int × Summand => match a.2 with
              | .variable j => a.1 * (ν j : Int)
              | _ => 0)).sum)
          simp only [Int.natAbs_mul, Int.natAbs_natCast] at hadd
          simp only [List.map_cons, List.sum_cons]
          have hw := Nat.mul_le_mul_left w.natAbs ha
          simp only [Summand.name] at hw
          nlinarith
      | phi i e =>
          simp only [List.map_cons, List.sum_cons, zero_add]
          exact ht.trans (Nat.mul_le_mul_right X (by omega))
      | hyperPhi i e f =>
          simp only [List.map_cons, List.sum_cons, zero_add]
          exact ht.trans (Nat.mul_le_mul_right X (by omega))

theorem linearPart_bound (r : Row) (ν : Nat → Nat) (X : Nat)
    (h : ∀ a ∈ r.2, ν a.2.name ≤ X) :
    (linearPart r ν).natAbs ≤ mass r * X + r.1.natAbs := by
  let t : Int := (r.2.map (fun a : Int × Summand => match a.2 with
    | .variable i => a.1 * (ν i : Int)
    | _ => 0)).sum
  have hs : t.natAbs ≤ mass r * X := linear_sum_bound r.2 ν X h
  change (r.1 + t).natAbs ≤ mass r * X + r.1.natAbs
  have hadd : (r.1 + t).natAbs ≤ r.1.natAbs + t.natAbs := Int.natAbs_add_le r.1 t
  omega

private theorem member_le_sum (xs : List Nat) (x : Nat) (h : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => simp at h
  | cons y xs ih =>
      rcases List.mem_cons.mp h with h | h
      · subst y
        simp
      · have hi := ih h
        simp only [List.sum_cons]
        omega

theorem active_below_leader (i : Nat) (r : Row) (ν : Nat → Nat)
    (ha : active i r ν = true) (leader : Int × Nat)
    (hmax : ∀ a ∈ CommonHeadCollectedRow.collect (phiData r ν), a.2 ≤ leader.2) :
    ν i ≤ leader.2 + shiftMass r := by
  obtain ⟨a, ha, ht⟩ := List.any_eq_true.mp ha
  rcases a with ⟨w, s⟩
  cases s with
  | «variable» j => simp [active] at ht
  | hyperPhi j e f => simp [active] at ht
  | phi j e =>
      have hh := Bool.and_eq_true_iff.mp ht
      have hji : j = i := by simpa only [beq_iff_eq] using hh.1
      subst j
      have hc : CommonHeadCollectedRow.coefficient (phiData r ν) (argument ν i e) ≠ 0 := by
        simpa only [bne_iff_ne] using hh.2
      have hm : (w, argument ν i e) ∈ phiData r ν :=
        List.mem_flatMap.mpr ⟨(w, Summand.phi i e), ha, by simp⟩
      have hk : argument ν i e ∈ CommonHeadCollectedRow.keys (phiData r ν) := by
        simp only [CommonHeadCollectedRow.keys, List.mem_dedup]
        exact List.mem_map.mpr ⟨(w, argument ν i e), hm, rfl⟩
      have hb : (CommonHeadCollectedRow.coefficient (phiData r ν) (argument ν i e),
          argument ν i e) ∈ CommonHeadCollectedRow.collect (phiData r ν) := by
        apply List.mem_filter.mpr
        refine ⟨List.mem_map.mpr ⟨argument ν i e, hk, rfl⟩, ?_⟩
        simpa only [bne_iff_ne] using hc
      have harg := hmax _ hb
      have he : e.natAbs ≤ shiftMass r := by
        apply member_le_sum
        exact List.mem_map.mpr ⟨(w, Summand.phi i e), ha, rfl⟩
      have hn := Int.le_natAbs (a := -e)
      have hz := Int.self_le_toNat ((ν i : Int) + e)
      simp only [Int.natAbs_neg] at hn
      dsimp only [argument] at harg
      omega

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainPhiDominanceProof
