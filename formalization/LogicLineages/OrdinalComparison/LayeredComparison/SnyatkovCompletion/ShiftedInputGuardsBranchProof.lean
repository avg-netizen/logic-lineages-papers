module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputGuardsInputProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainPhiDominanceSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputGuardsProof
open NormalForm ShiftedInputGuards CommonHeadLargeGuards CommonHeadCollectedRow

private theorem maximal_eval (cs : List Int) (i : Nat) (ν : Nat → Nat) :
    (maximalFormula cs i).eval ν ↔
      ∀ j < cs.length, ¬ν i < ν j ∨ coefficient (inputRow cs ν) (ν j) = 0 := by
  simp only [maximalFormula, CommonHeadLargeGuards.Proof.conjunction_eval,
    List.mem_map, List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    CommonHeadLargeGuards.Formula.eval, block_eval,
    Int.sign_eq_zero_iff_zero]

private theorem sign_eval (cs : List Int) (desired : Int) (ν : Nat → Nat) :
    (signFormula 0 cs desired).eval ν ↔
      (0 = desired ∧ collect (inputRow cs ν) = []) ∨
      (desired ≠ 0 ∧ ∃ i < cs.length,
        Int.sign (coefficient (inputRow cs ν) (ν i)) = desired ∧
          (maximalFormula cs i).eval ν) := by
  have htruth (P : Prop) [Decidable P] :
      (if P then CommonHeadLargeGuards.Formula.truth else .falsity).eval ν ↔ P := by
    by_cases h : P <;> simp [h, CommonHeadLargeGuards.Formula.eval]
  simp only [signFormula, CommonHeadLargeGuards.Formula.eval, htruth, canceled_eval,
    Int.sign_zero]
  by_cases hd : desired = 0
  · simp only [if_true, CommonHeadLargeGuards.Formula.eval, hd, ne_eq,
      not_true_eq_false, false_and, or_false]
  · simp [hd, CommonHeadLargeGuards.Proof.disjunction_eval,
      CommonHeadLargeGuards.Formula.eval, block_eval]

private theorem exists_greatest (row : CommonHeadLargeRow.Row) (hne : row ≠ []) :
    ∃ a ∈ row, ∀ b ∈ row, b.2 ≤ a.2 := by
  induction row with
  | nil => exact False.elim (hne rfl)
  | cons a row ih =>
      by_cases hr : row = []
      · subst row
        exact ⟨a, List.mem_cons_self, by simp⟩
      · obtain ⟨b, hb, hmax⟩ := ih hr
        by_cases hab : a.2 ≤ b.2
        · refine ⟨b, List.mem_cons_of_mem _ hb, ?_⟩
          intro c hc
          rcases List.mem_cons.mp hc with h | h
          · subst c; exact hab
          · exact hmax c h
        · refine ⟨a, List.mem_cons_self, ?_⟩
          intro c hc
          rcases List.mem_cons.mp hc with h | h
          · subst c; exact le_rfl
          · exact (hmax c h).trans (by omega)

/-- A finite collection lemma. The numerical row theorem supplies hsign below;
the frozen source target itself does not assume a tail sign oracle. -/
private theorem active_sign_eval (cs : List Int) (ν : Nat → Nat) (R : Int)
    (hne : collect (inputRow cs ν) ≠ [])
    (hsign : ∀ a ∈ collect (inputRow cs ν),
      (∀ b ∈ collect (inputRow cs ν), b.2 ≤ a.2) → Int.sign R = Int.sign a.1)
    (desired : Int) :
    (signFormula 0 cs desired).eval ν ↔ Int.sign R = desired := by
  have hsupport := CommonHeadCollectedRow.Proof.literalCollectedSupport (inputRow cs ν)
  rw [sign_eval]
  constructor
  · rintro (⟨_, hempty⟩ | ⟨hd, i, hi, hcoef, hmax⟩)
    · exact False.elim (hne hempty)
    · have hn : coefficient (inputRow cs ν) (ν i) ≠ 0 := by
        intro hz
        apply hd
        rw [← hcoef, hz, Int.sign_zero]
      have ha := collected_at (inputRow cs ν) (ν i)
        ⟨(cs[i], ν i), input_at cs ν i hi, rfl⟩ hn
      have hgreat : ∀ b ∈ collect (inputRow cs ν), b.2 ≤ ν i := by
        intro b hb
        by_contra hnot
        have hlt : ν i < b.2 := lt_of_not_ge hnot
        obtain ⟨hbnon, hbcoef, c, hc, hcb⟩ := hsupport.2.1 b hb
        obtain ⟨j, hj, hej⟩ := input_member cs ν c hc
        have he : ν j = b.2 := hej.trans hcb
        rcases (maximal_eval cs i ν).mp hmax j hj with h | h
        · exact h (by simpa only [he] using hlt)
        · apply hbnon
          rw [hbcoef, ← he, h]
      exact (hsign _ ha hgreat).trans hcoef
  · intro hs
    obtain ⟨a, ha, hmax⟩ := exists_greatest _ hne
    have hsgn := hsign a ha hmax
    obtain ⟨hn, hcoef, b, hb, hba⟩ := hsupport.2.1 a ha
    obtain ⟨i, hi, hei⟩ := input_member cs ν b hb
    have he : ν i = a.2 := hei.trans hba
    have hd : desired ≠ 0 := by
      intro hz
      apply hn
      apply Int.eq_zero_of_sign_eq_zero
      exact hsgn.symm.trans (hs.trans hz)
    refine Or.inr ⟨hd, i, hi, ?_, ?_⟩
    · rw [he, ← hcoef]
      exact hsgn.symm.trans hs
    · apply (maximal_eval cs i ν).mpr
      intro j hj
      by_cases hlt : ν i < ν j
      · right
        by_contra hnon
        have hm := collected_at (inputRow cs ν) (ν j)
          ⟨(cs[j], ν j), input_at cs ν j hj, rfl⟩ hnon
        have hh := hmax _ hm
        rw [← he] at hh
        exact (not_le_of_gt hlt) hh
      · exact Or.inl hlt

private theorem active_nonempty (r : NormalForm.Row) (i : Nat) (ν : Nat → Nat)
    (hactive : PlainPhiDominance.active i r ν = true) :
    collect (PlainPhiDominance.phiData r ν) ≠ [] := by
  obtain ⟨a, ha, ht⟩ := List.any_eq_true.mp hactive
  rcases a with ⟨w, s⟩
  cases s with
  | «variable» j => simp [PlainPhiDominance.active] at ht
  | hyperPhi j e f => simp [PlainPhiDominance.active] at ht
  | phi j e =>
      have hn : coefficient (PlainPhiDominance.phiData r ν)
          (PlainPhiDominance.argument ν j e) ≠ 0 := by
        have hh := (Bool.and_eq_true_iff.mp ht).2
        simpa using hh
      have hm : (w, PlainPhiDominance.argument ν j e) ∈ PlainPhiDominance.phiData r ν := by
        apply List.mem_flatMap.mpr
        exact ⟨(w, .phi j e), ha, by simp⟩
      have hc := collected_at (PlainPhiDominance.phiData r ν)
        (PlainPhiDominance.argument ν j e) ⟨_, hm, rfl⟩ hn
      intro hz
      rw [hz] at hc
      exact List.not_mem_nil hc

theorem actualFiniteActiveBranch : ShiftedInputGuardsTargets.ActualFiniteActiveBranch := by
  intro r hp i ν hthreshold hframe hactive desired
  unfold activeSign
  rw [actualGuardCompilation]
  apply active_sign_eval (coefficients r) (valuation (inputs r) ν) (rowValue r ν)
  · rw [originalInputCalibration]
    exact active_nonempty r i ν hactive
  · rw [originalInputCalibration]
    exact PlainPhiDominanceProof.actualMaximalRawDominance r hp i ν hthreshold hframe hactive

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputGuardsProof
