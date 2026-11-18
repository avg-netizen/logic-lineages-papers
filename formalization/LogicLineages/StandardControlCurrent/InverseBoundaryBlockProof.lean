module
public import LogicLineages.StandardControlCurrent.InverseBoundaryBlockTargets
public import LogicLineages.StandardControlCurrent.MixedRunnerBlockProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.DominantBoundarySemanticProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.InverseBoundaryBlockProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion NonlinearProjectionCompletion
open InverseBoundaryBlock HyperCloseBlock

theorem actualBand : InverseBoundaryBlockTargets.ActualBand :=
  DominantBoundaryProof.actualFiniteBand

theorem singleElimination : InverseBoundaryBlockTargets.SingleElimination :=
  DominantBoundaryProof.actualNonlinearProjection

theorem blockElimination : InverseBoundaryBlockTargets.BlockElimination := by
  intro xs i a shift lower upper p hn hi ha hl hu ν
  exact MixedRunnerBlockProof.block_erase xs i
    (.conjunction (DominantBoundary.region i a shift lower upper) p)
    (DominantBoundary.project i a shift lower upper p) hn hi
    (DominantBoundaryProof.actualNonlinearProjection i a shift lower upper p ha hl hu) ν

theorem progressSupport : InverseBoundaryBlockTargets.ProgressSupport := by
  intro xs i a shift lower upper p hn hi ha hl hu
  have hlen := List.length_erase_add_one hi
  have hs := DominantBoundaryProof.exactParameterSupport i a shift lower upper p hl hu
  change (xs.erase i).Nodup ∧ (xs.erase i).length+1=xs.length ∧
    (xs.erase i).length<xs.length ∧
    i ∉ (DominantBoundary.project i a shift lower upper p).variables ∧ _
  refine ⟨List.Nodup.erase i hn,hlen,by omega,?_,?_⟩
  · intro hm
    exact (hs i hm).1 rfl
  · intro j hj hnot
    obtain ⟨hne,hmem⟩ := hs j hj
    refine ⟨?_,hmem⟩
    intro hxs
    exact hnot (hn.mem_erase_iff.mpr ⟨hne,hxs⟩)
end LogicLineages.StandardControlCurrent.InverseBoundaryBlockProof
