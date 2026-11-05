module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiRowsCoverageProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiRowsProof
open NormalForm InactivePhiRows

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

theorem literalLinearOutput : InactivePhiRowsTargets.LiteralLinearOutput := by
  intro i a
  apply any_linear
  intro p hp
  obtain ⟨mask, hm, rfl⟩ := List.mem_map.mp hp
  have hguard : LinearRows.isLinear i (guard a.row mask) = true :=
    ShiftedInputGuardsProof.literalGuardLinearity _ _ i
  have hrow := (mask_spec a.row i mask hm).2.2
  have hatom : LinearRows.isLinear i (.atom (withRow a (remaining a.row mask))) = true := by
    cases a <;> simpa [withRow, LinearRows.isLinear, LinearRows.atoms, Atom.row] using hrow
  simpa only [LinearRows.isLinear, LinearRows.atoms, List.all_append] using
    Bool.and_eq_true_iff.mpr ⟨hguard, hatom⟩

private theorem withRow_eval (a : Atom) (r : Row) (ν : Nat → Nat)
    (he : rowValue r ν = rowValue a.row ν) :
    (withRow a r).eval ν ↔ a.eval ν := by
  cases a <;> simp only [withRow, Atom.eval, Atom.row] at he ⊢ <;> rw [he]

theorem actualInactiveAtom : InactivePhiRowsTargets.ActualInactiveAtom := by
  intro i a hp ν hi
  unfold compileAtom
  rw [BoundedRowsSemanticProof.any_eval]
  constructor
  · rintro ⟨p, hm, hg⟩
    obtain ⟨mask, hm, rfl⟩ := List.mem_map.mp hm
    have hv := guardedValuePreservation a.row i mask hm ν hg.1
    exact (withRow_eval a _ ν hv).mp hg.2
  · intro ha
    obtain ⟨mask, hm, hg⟩ := finiteInactiveCoverage a.row hp i ν hi
    refine ⟨_, List.mem_map.mpr ⟨mask, hm, rfl⟩, hg, ?_⟩
    have hv := guardedValuePreservation a.row i mask hm ν hg
    exact (withRow_eval a _ ν hv).mpr ha

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiRowsProof
