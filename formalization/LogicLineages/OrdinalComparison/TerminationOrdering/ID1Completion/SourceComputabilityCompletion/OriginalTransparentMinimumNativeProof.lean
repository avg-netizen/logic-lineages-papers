module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentativeGlobalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumNativeProof
open UniformCertificateCompletion OriginalTransparentMinimum
open OriginalTransparentMinimumCalibrationProof
open OriginalRankGuardedRepresentativeNativeProof OriginalRankGuardedRepresentativeGlobalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualOriginalTransparentMinimumLiteralFields :
    OriginalTransparentMinimumTargets.ActualOriginalTransparentMinimumLiteralFields := by
  intro p H G W P
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem actualOriginalTransparentMinimumNativePreparation :
    OriginalTransparentMinimumTargets.ActualOriginalTransparentMinimumNativePreparation := by
  intro n arity p H G P hp hH hG hP
  have he : ∀ v : List.Vector Nat 2,
      evaluate (minimumInputs H G P p).base.oldRepresentative v =
        evaluate p.base.oldRepresentative v := by
    intro v
    exact (actualOriginalTransparentMinimumCalibration n arity H G P hH hG hP v).trans
      (hp.1.2.2.1 v).symm
  exact ⟨he,⟨⟨hp.1.1,hp.1.2.1,
    fun v => (he v).trans (hp.1.2.2.1 v),hp.1.2.2.2⟩,hp.2⟩⟩

/-- Reconstruct every prior rank-guard property at the explicitly supplied
minimum-input tuple; never choose a second package or final pipeline. -/
theorem actualOriginalTransparentMinimumRetention :
    OriginalTransparentMinimumTargets.ActualOriginalTransparentMinimumRetention := by
  intro n arity p H G W P hp hH hG hW hP
  let s := minimumInputs H G P p
  have hs := (actualOriginalTransparentMinimumNativePreparation n arity p H G P hp hH hG hP).2
  exact ⟨transparentProperties n arity s H G W hs hH hG hW,
    actualOriginalRankGuardedRepresentativeLiteralFields s H G W,
    actualOriginalRankGuardedRepresentativeNativePreparation n arity s H G W hs hH hG hW,
    OriginalRankGuardedRepresentativeInternalProof.actualOriginalRankGuardedRepresentativeInternalRank s H G W,
    actualOriginalRankGuardedRepresentativeRetention n arity s H G W hs hH hG hW⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumNativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMinimumNativeProof
