module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputGuardsSemanticProof
public import LogicLineages.OrdinalComparison.CommonHeadLargeGuardsMaskProof
public import LogicLineages.OrdinalComparison.CommonHeadCollectedRowAlgebraProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputGuardsProof
open NormalForm ShiftedInputGuards

private theorem indexed_inputs (xs : List (Int × Input)) (ν : Nat → Nat) :
    CommonHeadLargeGuards.inputRow (xs.map Prod.fst) (valuation (xs.map Prod.snd) ν) =
      xs.map (fun a => (a.1, value a.2 ν)) := by
  apply List.ext_getElem
  · simp [CommonHeadLargeGuards.inputRow]
  · intro j hj hk
    have hx : j < xs.length := by simpa [CommonHeadLargeGuards.inputRow] using hj
    have hm : j < (xs.map Prod.snd).length := by simpa using hx
    simp only [CommonHeadLargeGuards.inputRow, List.getElem_map, List.getElem_zipIdx,
      Nat.zero_add, valuation, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm,
      Option.getD_some]

theorem originalInputCalibration : ShiftedInputGuardsTargets.OriginalInputCalibration := by
  intro r ν
  unfold coefficients inputs
  rw [indexed_inputs]
  rcases r with ⟨z, xs⟩
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      rcases a with ⟨w, s⟩
      cases s <;> simp only [occurrences, PlainPhiDominance.phiData, List.flatMap_cons,
        List.nil_append, List.singleton_append, List.map_cons, value,
        PlainPhiDominance.argument] at ih ⊢
      · exact ih
      · exact congrArg (List.cons (w, ((ν _ : Int) + _).toNat)) ih
      · exact ih

theorem input_member (cs : List Int) (ν : Nat → Nat) (a : Int × Nat)
    (ha : a ∈ CommonHeadLargeGuards.inputRow cs ν) : ∃ i < cs.length, ν i = a.2 := by
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact ⟨b.2, by simpa using List.snd_lt_of_mem_zipIdx hb, rfl⟩

theorem input_at (cs : List Int) (ν : Nat → Nat) (i : Nat) (hi : i < cs.length) :
    (cs[i], ν i) ∈ CommonHeadLargeGuards.inputRow cs ν := by
  apply List.mem_map.mpr
  refine ⟨(cs[i], i), ?_, rfl⟩
  exact List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi)

theorem collected_at (row : CommonHeadLargeRow.Row) (t : Nat)
    (hkey : ∃ b ∈ row, b.2 = t) (hne : CommonHeadCollectedRow.coefficient row t ≠ 0) :
    (CommonHeadCollectedRow.coefficient row t, t) ∈ CommonHeadCollectedRow.collect row := by
  apply List.mem_filter.mpr
  refine ⟨List.mem_map.mpr ⟨t, ?_, rfl⟩, ?_⟩
  · simp only [CommonHeadCollectedRow.keys, List.mem_dedup]
    exact List.mem_map.mpr hkey
  · simpa using hne

theorem block_eval (cs : List Int) (i : Nat) (desired : Int) (ν : Nat → Nat) :
    (CommonHeadLargeGuards.blockFormula cs i desired).eval ν ↔ Int.sign
      (CommonHeadCollectedRow.coefficient (CommonHeadLargeGuards.inputRow cs ν) (ν i)) = desired :=
  CommonHeadLargeGuards.Proof.exactBlockFormula cs i desired ν

theorem canceled_eval (cs : List Int) (ν : Nat → Nat) :
    (CommonHeadLargeGuards.canceledFormula cs).eval ν ↔
      CommonHeadCollectedRow.collect (CommonHeadLargeGuards.inputRow cs ν) = [] := by
  have he : (CommonHeadLargeGuards.canceledFormula cs).eval ν ↔
      ∀ i < cs.length, CommonHeadCollectedRow.coefficient
        (CommonHeadLargeGuards.inputRow cs ν) (ν i) = 0 := by
    simp only [CommonHeadLargeGuards.canceledFormula,
      CommonHeadLargeGuards.Proof.conjunction_eval, List.mem_map, List.mem_range,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      block_eval, Int.sign_eq_zero_iff_zero]
  rw [he]
  constructor
  · intro hz
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro a ha
    obtain ⟨hn, hcoef, b, hb, hba⟩ :=
      (CommonHeadCollectedRow.Proof.literalCollectedSupport (CommonHeadLargeGuards.inputRow cs ν)).2.1 a ha
    obtain ⟨i, hi, heq⟩ := input_member cs ν b hb
    apply hn
    rw [hcoef, ← hba, ← heq, hz i hi]
  · intro hempty i hi
    by_contra hn
    have hm := collected_at (CommonHeadLargeGuards.inputRow cs ν) (ν i)
      ⟨(cs[i], ν i), input_at cs ν i hi, rfl⟩ hn
    rw [hempty] at hm
    exact List.not_mem_nil hm

theorem actualCancellationGuard : ShiftedInputGuardsTargets.ActualCancellationGuard := by
  intro r ν
  unfold canceled
  rw [actualGuardCompilation, canceled_eval, originalInputCalibration]

theorem actualBlockGuard : ShiftedInputGuardsTargets.ActualBlockGuard := by
  intro r k desired ν
  unfold block
  rw [actualGuardCompilation, CommonHeadLargeGuards.Proof.exactBlockFormula,
    originalInputCalibration]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputGuardsProof
