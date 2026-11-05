module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainLinearCleanupSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchProvenanceBranchProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainLinearCleanupProof
open NormalForm PlainLinearCleanup PlainBranchProvenance

theorem nonlinear_occurrences_cleanup (p : Formula) (s : Summand) :
    s ∈ nonlinearOccurrences (cleanup p) ↔ s ∈ nonlinearOccurrences p := by
  constructor
  · intro hs
    obtain ⟨hs, hn⟩ := (PlainBranchProvenanceProof.mem_nonlinear _ s).mp hs
    have h := (LinearBlockProof.exactBlockOccurrences (linearNames p) p s).mp hs
    exact (PlainBranchProvenanceProof.mem_nonlinear p s).mpr ⟨h.2, hn⟩
  · intro hs
    have h := (PlainBranchProvenanceProof.mem_nonlinear p s).mp hs
    have hnot : s.name ∉ linearNames p := by
      intro hn
      have hl := ((exactLinearSelection p s.name).mp hn).2
      exact ((PlainBranchProvenanceProof.exactLinearityDetection s.name p).mp hl s hs) rfl
    exact (PlainBranchProvenanceProof.mem_nonlinear _ s).mpr
      ⟨(LinearBlockProof.exactBlockOccurrences (linearNames p) p s).mpr ⟨hnot, h.1⟩, h.2⟩

theorem exactNonlinearNames : PlainLinearCleanupTargets.ExactNonlinearNames := by
  intro p
  apply Finset.ext
  intro i
  simp only [PlainBranchProvenanceProof.mem_nonlinearNames, nonlinear_occurrences_cleanup]

private theorem block_linearity_other (names : List Nat) (p : Formula) (i : Nat)
    (hi : i ∉ names) :
    LinearRows.isLinear i (LinearBlock.eliminate names p) = LinearRows.isLinear i p := by
  induction names with
  | nil => rfl
  | cons j names ih =>
      have hij : i ≠ j := fun h => hi (List.mem_cons.mpr (Or.inl h))
      have hrest : i ∉ names := fun h => hi (List.mem_cons_of_mem j h)
      change LinearRows.isLinear i (LinearRows.eliminate j (LinearBlock.eliminate names p)) = _
      rw [LinearBlockProof.exactLinearityAfterElimination, if_neg hij]
      exact ih hrest

theorem noLinearNames : PlainLinearCleanupTargets.NoLinearNames := by
  intro p i hi
  have hs := (LinearBlockProof.exactBlockSupport (linearNames p) p i).mp hi
  change LinearRows.isLinear i (LinearBlock.eliminate (linearNames p) p) = false
  rw [block_linearity_other (linearNames p) p i hs.1]
  cases h : LinearRows.isLinear i p with
  | false => rfl
  | true => exact False.elim (hs.1 ((exactLinearSelection p i).mpr ⟨hs.2, h⟩))

theorem preservePlain : PlainLinearCleanupTargets.PreservePlain := by
  intro p hp
  apply (PlainBranchProvenanceProof.exactPlainDetection _).mpr
  intro s hs
  exact (PlainBranchProvenanceProof.exactPlainDetection p).mp hp s
    ((LinearBlockProof.exactBlockOccurrences (linearNames p) p s).mp hs).2

theorem groundCriterion : PlainLinearCleanupTargets.GroundCriterion := by
  intro p hp
  have hn : nonlinearNames (cleanup p) = ∅ := (exactNonlinearNames p).trans hp
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro i hi
  have hl : LinearRows.isLinear i (cleanup p) = true := by
    apply (PlainBranchProvenanceProof.exactLinearityDetection i (cleanup p)).mpr
    intro s hs
    have hm : s.name ∈ nonlinearNames (cleanup p) :=
      (PlainBranchProvenanceProof.mem_nonlinearNames _ s.name).mpr ⟨s, hs, rfl⟩
    rw [hn] at hm
    simp at hm
  rw [noLinearNames p i hi] at hl
  cases hl

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainLinearCleanupProof
