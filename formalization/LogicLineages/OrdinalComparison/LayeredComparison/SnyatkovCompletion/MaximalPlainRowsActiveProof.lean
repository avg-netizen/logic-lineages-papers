module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputGuardsBranchProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainRowsProof
open NormalForm MaximalPlainRows

private theorem occurrence_mem (r : Row) (w : Int) (j : Nat) (e : Int) :
    (w, j, e) ∈ ShiftedInputGuards.occurrences r ↔ (w, Summand.phi j e) ∈ r.2 := by
  rcases r with ⟨z, xs⟩
  induction xs with
  | nil => simp [ShiftedInputGuards.occurrences]
  | cons a xs ih =>
      rcases a with ⟨v, s⟩
      cases s <;> simp_all [ShiftedInputGuards.occurrences]

private theorem input_get (r : Row) (k : Nat) (hk : k < (ShiftedInputGuards.occurrences r).length) :
    (ShiftedInputGuards.inputs r).getD k (0, 0) = (ShiftedInputGuards.occurrences r)[k].2 := by
  simp [ShiftedInputGuards.inputs, List.getD_eq_getElem?_getD, hk]

theorem exactActiveGuard : MaximalPlainRowsTargets.ExactActiveGuard := by
  intro i r ν
  unfold activeGuard
  rw [BoundedRowsSemanticProof.any_eval]
  constructor
  · rintro ⟨p, hp, hnot⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    have hown := List.mem_filter.mp hk
    have hindex := List.mem_range.mp hown.1
    have hname : ((ShiftedInputGuards.inputs r).getD k (0, 0)).1 = i := by
      simpa using hown.2
    have hc : CommonHeadCollectedRow.coefficient (PlainPhiDominance.phiData r ν)
        (ShiftedInputGuards.valuation (ShiftedInputGuards.inputs r) ν k) ≠ 0 := by
      intro hz
      apply hnot
      apply (ShiftedInputGuardsProof.actualBlockGuard r k 0 ν).mpr
      rw [hz, Int.sign_zero]
    rcases hitem : (ShiftedInputGuards.occurrences r)[k] with ⟨w, j, e⟩
    have hget := input_get r k hindex
    rw [hitem] at hget
    have hj : j = i := by simpa only [hget] using hname
    have horig : (w, Summand.phi j e) ∈ r.2 :=
      (occurrence_mem r w j e).mp (by rw [← hitem]; exact List.getElem_mem hindex)
    have hv : ShiftedInputGuards.valuation (ShiftedInputGuards.inputs r) ν k =
        PlainPhiDominance.argument ν j e := by
      simp only [ShiftedInputGuards.valuation, hget, ShiftedInputGuards.value,
        PlainPhiDominance.argument]
    rw [hv] at hc
    subst j
    apply List.any_eq_true.mpr
    exact ⟨(w, .phi i e), horig, by simpa using hc⟩
  · intro hactive
    obtain ⟨a, ha, ht⟩ := List.any_eq_true.mp hactive
    rcases a with ⟨w, s⟩
    cases s with
    | «variable» j => simp at ht
    | hyperPhi j e f => simp at ht
    | phi j e =>
        have hh := Bool.and_eq_true_iff.mp ht
        have hj : j = i := by simpa using hh.1
        have hc : CommonHeadCollectedRow.coefficient (PlainPhiDominance.phiData r ν)
            (PlainPhiDominance.argument ν j e) ≠ 0 := by simpa using hh.2
        subst j
        obtain ⟨k, hk, he⟩ := List.getElem_of_mem ((occurrence_mem r w i e).mpr ha)
        have hget := input_get r k hk
        rw [he] at hget
        have hown : k ∈ ownIndices i r :=
          List.mem_filter.mpr ⟨List.mem_range.mpr hk, by simp only [hget, beq_self_eq_true]⟩
        refine ⟨_, List.mem_map.mpr ⟨k, hown, rfl⟩, ?_⟩
        intro hz
        have hs := (ShiftedInputGuardsProof.actualBlockGuard r k 0 ν).mp hz
        apply hc
        apply Int.eq_zero_of_sign_eq_zero
        simpa only [ShiftedInputGuards.valuation, hget, ShiftedInputGuards.value,
          PlainPhiDominance.argument] using hs

private theorem any_linear (i : Nat) (ps : List Formula)
    (h : ∀ p ∈ ps, LinearRows.isLinear i p = true) :
    LinearRows.isLinear i (BoundedRows.any ps) = true := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      have hp := h p List.mem_cons_self
      have hps := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      simpa only [BoundedRows.any, List.foldr_cons, LinearRows.isLinear,
        LinearRows.atoms, List.all_append] using Bool.and_eq_true_iff.mpr ⟨hp, hps⟩

theorem activeGuard_linear (i j : Nat) (r : Row) :
    LinearRows.isLinear j (activeGuard i r) = true := by
  apply any_linear
  intro p hp
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hp
  exact ShiftedInputGuardsProof.literalGuardLinearity _ _ j

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainRowsProof
