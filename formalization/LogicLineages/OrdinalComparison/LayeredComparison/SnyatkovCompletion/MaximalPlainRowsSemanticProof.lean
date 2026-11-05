module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainRowsActiveProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainRowsResidueProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiRowsSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainRowsProof
open NormalForm MaximalPlainRows

private theorem inactive_nonnegative_sound (i : Nat) (r : Row) (ν : Nat → Nat)
    (h : (InactivePhiRows.compileAtom i (.nonnegative r)).eval ν) : 0 ≤ rowValue r ν := by
  unfold InactivePhiRows.compileAtom at h
  rw [BoundedRowsSemanticProof.any_eval] at h
  obtain ⟨p, hp, hv⟩ := h
  obtain ⟨mask, hmask, rfl⟩ := List.mem_map.mp hp
  have he := InactivePhiRowsProof.guardedValuePreservation r i mask hmask ν hv.1
  have hv' : 0 ≤ rowValue (InactivePhiRows.remaining r mask) ν := hv.2
  rwa [he] at hv'

private theorem nonnegative_sign (z : Int) : (Int.sign z = 0 ∨ Int.sign z = 1) ↔ 0 ≤ z := by
  rw [Int.sign_eq_zero_iff_zero, Int.sign_eq_one_iff_pos]
  omega

theorem nonnegative_eval (i : Nat) (r : Row) (hp : PlainPhiDominance.isPlain r = true)
    (ν : Nat → Nat) (hcut : PlainPhiDominance.threshold r ≤ ν i)
    (hframe : ∀ a ∈ r.2, ν a.2.name ≤ ν i) :
    (nonnegative i r).eval ν ↔ 0 ≤ rowValue r ν := by
  constructor
  · intro h
    rcases h with h | ⟨ha, hs⟩
    · exact inactive_nonnegative_sound i r ν h
    · have hactive := (exactActiveGuard i r ν).mp ha
      apply (nonnegative_sign _).mp
      exact (or_congr
        (ShiftedInputGuardsProof.actualFiniteActiveBranch r hp i ν hcut hframe hactive 0)
        (ShiftedInputGuardsProof.actualFiniteActiveBranch r hp i ν hcut hframe hactive 1)).mp hs
  · intro hz
    cases hactive : PlainPhiDominance.active i r ν with
    | false =>
        exact Or.inl ((InactivePhiRowsProof.actualInactiveAtom i (.nonnegative r) hp ν hactive).mpr hz)
    | true =>
        refine Or.inr ⟨(exactActiveGuard i r ν).mpr hactive, ?_⟩
        exact (or_congr
          (ShiftedInputGuardsProof.actualFiniteActiveBranch r hp i ν hcut hframe hactive 0)
          (ShiftedInputGuardsProof.actualFiniteActiveBranch r hp i ν hcut hframe hactive 1)).mpr
          ((nonnegative_sign _).mpr hz)

theorem actualMaximalTailAtom : MaximalPlainRowsTargets.ActualMaximalTailAtom := by
  intro i a hp ν hcut hframe
  cases a with
  | nonnegative r => exact nonnegative_eval i r hp ν hcut hframe
  | divisible m r =>
      have hres := actualSignedRowResidue i (m + 1) (by omega) r ν hcut
      exact hres.dvd_iff.symm

theorem literalTailLinearity : MaximalPlainRowsTargets.LiteralTailLinearity := by
  intro i a hp
  cases a with
  | nonnegative r =>
      have hinactive := InactivePhiRowsProof.literalLinearOutput i (.nonnegative r)
      have hactive := activeGuard_linear i i r
      have hzero : LinearRows.isLinear i (ShiftedInputGuards.activeSign r 0) = true :=
        ShiftedInputGuardsProof.literalGuardLinearity _ _ i
      have hone : LinearRows.isLinear i (ShiftedInputGuards.activeSign r 1) = true :=
        ShiftedInputGuardsProof.literalGuardLinearity _ _ i
      simpa only [compileAtom, nonnegative, LinearRows.isLinear, LinearRows.atoms,
        List.all_append] using
        Bool.and_eq_true_iff.mpr ⟨hinactive,
          Bool.and_eq_true_iff.mpr ⟨hactive, Bool.and_eq_true_iff.mpr ⟨hzero, hone⟩⟩⟩
  | divisible m r =>
      have h := residueRow_linear i (m + 1) r hp
      simpa [compileAtom, LinearRows.isLinear, LinearRows.atoms, Atom.row] using h

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainRowsProof
