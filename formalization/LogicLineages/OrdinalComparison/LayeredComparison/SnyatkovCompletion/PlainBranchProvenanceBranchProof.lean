module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchProvenanceAtomicProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchFrameProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchProvenanceProof
open NormalForm PlainBranchProvenance

private theorem maxima_noNonlinear (i : Nat) (xs : List Nat) :
    nonlinearOccurrences (xs.foldr (fun j rest =>
      Formula.conjunction (MaximalPlainBranch.maximumGuard i j) rest) .truth) = [] := by
  induction xs with
  | nil => rfl
  | cons j xs ih =>
      have hg := allLinear_noNonlinear _ (MaximalPlainBranchProof.maximumGuard_linear i j)
      simp only [List.foldr_cons, nonlinear_conjunction, hg, ih, List.nil_append]

theorem frame_noNonlinear (i : Nat) (p : Formula) :
    nonlinearOccurrences (MaximalPlainBranch.frame i p) = [] := by
  have hl := allLinear_noNonlinear _ (MaximalPlainBranchProof.lowerGuard_linear i (MaximalPlainBranch.cutoff p))
  simp only [MaximalPlainBranch.frame, nonlinear_conjunction, hl, maxima_noNonlinear, List.nil_append]

theorem compile_provenance (i : Nat) (p : Formula) (s : Summand) :
    s ∈ nonlinearOccurrences (MaximalPlainBranch.compile i p) → s ∈ nonlinearOccurrences p := by
  induction p with
  | truth => exact id
  | falsity => exact id
  | atom a => exact literalAtomicProvenance i a s
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
      simpa only [MaximalPlainBranch.compile, nonlinear_conjunction, List.mem_append] using Or.imp ihp ihq
  | disjunction p q ihp ihq =>
      simpa only [MaximalPlainBranch.compile, nonlinear_disjunction, List.mem_append] using Or.imp ihp ihq

theorem literalBranchProvenance : PlainBranchProvenanceTargets.LiteralBranchProvenance := by
  intro i p s hs
  obtain ⟨hs, hn⟩ := (mem_nonlinear _ s).mp hs
  have h := (LinearBlockProof.exactOneNameOccurrences i (MaximalPlainBranch.framed i p) s).mp hs
  have hf := (mem_nonlinear (MaximalPlainBranch.framed i p) s).mpr ⟨h.2, hn⟩
  simp only [MaximalPlainBranch.framed, nonlinear_conjunction, frame_noNonlinear, List.nil_append] at hf
  exact ⟨h.1, compile_provenance i p s hf⟩

theorem preservePlain : PlainBranchProvenanceTargets.PreservePlain := by
  intro i p hp
  apply (exactPlainDetection _).mpr
  intro s hs
  by_cases hn : nonlinear s = true
  · have h := literalBranchProvenance i p s ((mem_nonlinear _ s).mpr ⟨hs, hn⟩)
    exact (exactPlainDetection p).mp hp s ((mem_nonlinear p s).mp h.2).1
  · cases s <;> simp_all [nonlinear, plain]

theorem mem_nonlinearNames (p : Formula) (i : Nat) :
    i ∈ nonlinearNames p ↔ ∃ s ∈ nonlinearOccurrences p, s.name = i := by
  simp only [nonlinearNames, List.mem_toFinset, List.mem_map]

theorem strictNameDecrease : PlainBranchProvenanceTargets.StrictNameDecrease := by
  intro i p hi
  have hsub : nonlinearNames (MaximalPlainBranch.eliminate i p) ⊆ nonlinearNames p := by
    intro j hj
    obtain ⟨s, hs, rfl⟩ := (mem_nonlinearNames _ j).mp hj
    exact (mem_nonlinearNames p s.name).mpr ⟨s, (literalBranchProvenance i p s hs).2, rfl⟩
  have hnot : i ∉ nonlinearNames (MaximalPlainBranch.eliminate i p) := by
    intro h
    obtain ⟨s, hs, he⟩ := (mem_nonlinearNames _ i).mp h
    exact (literalBranchProvenance i p s hs).1 he
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hsub, ?_⟩
  intro he
  apply hnot
  rw [he]
  exact hi

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchProvenanceProof
