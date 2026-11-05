module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchProvenanceDetectionProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainRowsSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchProvenanceProof
open NormalForm PlainBranchProvenance

private theorem withRow_row (a : Atom) (r : Row) : (InactivePhiRows.withRow a r).row = r := by
  cases a <;> rfl

theorem inactive_provenance (i : Nat) (a : Atom) (s : Summand)
    (hs : s ∈ nonlinearOccurrences (InactivePhiRows.compileAtom i a)) :
    s ∈ nonlinearOccurrences (.atom a) := by
  obtain ⟨hs, hn⟩ := (mem_nonlinear _ s).mp hs
  obtain ⟨p, hp, hs⟩ := (LinearBlockProof.any_occurrences _ s).mp hs
  obtain ⟨mask, _, rfl⟩ := List.mem_map.mp hp
  have hbranch : s ∈ nonlinearOccurrences
      (.conjunction (InactivePhiRows.guard a.row mask)
        (.atom (InactivePhiRows.withRow a (InactivePhiRows.remaining a.row mask)))) :=
    (mem_nonlinear _ s).mpr ⟨hs, hn⟩
  rw [nonlinear_conjunction] at hbranch
  rcases List.mem_append.mp hbranch with hg | ha
  · have hz : nonlinearOccurrences (InactivePhiRows.guard a.row mask) = [] := linearGuards _ _
    rw [hz] at hg
    exact False.elim (List.not_mem_nil hg)
  · have ho := (mem_nonlinear _ s).mp ha
    obtain ⟨b, hb, he⟩ := (mem_atom _ s).mp ho.1
    rw [withRow_row] at hb
    have hb' := (InactivePhiRowsProof.literalRetainedOccurrences a.row mask).1 b hb
    exact (mem_nonlinear _ s).mpr ⟨(mem_atom a s).mpr ⟨b, hb', he⟩, hn⟩

theorem activeGuard_noNonlinear (i : Nat) (r : Row) :
    nonlinearOccurrences (MaximalPlainRows.activeGuard i r) = [] :=
  allLinear_noNonlinear _ (fun j => MaximalPlainRowsProof.activeGuard_linear i j r)

theorem nonnegative_provenance (i : Nat) (r : Row) (s : Summand)
    (hs : s ∈ nonlinearOccurrences (MaximalPlainRows.nonnegative i r)) :
    s ∈ nonlinearOccurrences (.atom (.nonnegative r)) := by
  have hz : nonlinearOccurrences (ShiftedInputGuards.activeSign r 0) = [] := linearGuards _ _
  have ho : nonlinearOccurrences (ShiftedInputGuards.activeSign r 1) = [] := linearGuards _ _
  simp only [MaximalPlainRows.nonnegative, nonlinear_disjunction, nonlinear_conjunction,
    activeGuard_noNonlinear, hz, ho, List.nil_append, List.append_nil] at hs
  exact inactive_provenance i (.nonnegative r) s hs

theorem literalAtomicProvenance : PlainBranchProvenanceTargets.LiteralAtomicProvenance := by
  intro i a s hs
  cases a with
  | nonnegative r => exact nonnegative_provenance i r s hs
  | divisible m r =>
      have h := (mem_nonlinear _ s).mp hs
      obtain ⟨b, hb, he⟩ := (mem_atom (.divisible m (MaximalPlainRows.residueRow i (m + 1) r)) s).mp h.1
      change b ∈ (MaximalPlainRows.residueRow i (m + 1) r).2 at hb
      rw [MaximalPlainRowsProof.exactResidualOccurrences i (m + 1) r] at hb
      have hb' := (List.mem_filter.mp hb).1
      exact (mem_nonlinear _ s).mpr ⟨(mem_atom (.divisible m r) s).mpr ⟨b, hb', he⟩, h.2⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchProvenanceProof
