module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedMinimumInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankCompletionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedMinimumGlobalProof
open UniformCertificateCompletion
open OriginalActiveObservedMinimumTargets
open OriginalRankGuardedRepresentativeGlobalProof OriginalRankGuardedRepresentativeNativeProof
open OriginalTransparentMinimumNativeProof OriginalTransparentMinimumGlobalProof
open OriginalFinalGuardedRankCompletionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Assemble the original minimum package and the final rank laws at the
literal same minimum-input tuple. The active observer is calibrated on every
input vector; the internal minimum law is supplied independently. -/
theorem actualOriginalActiveObservedMinimumRetention :
    ActualOriginalActiveObservedMinimumRetention := by
  intro n arity p H G W P hp hH hG hW hP
  let Q := OriginalActiveObservedClass.classTest p H G W
    OriginalRawSyntaxTransport.variableRankPackedRaw P
  let s := OriginalTransparentMinimum.minimumInputs H G Q p
  have hQ : OriginalTransparentMinimum.ClassTestCalibrated n arity Q :=
    OriginalActiveObservedCalibrationProof.actualOriginalActiveObservedRankCalibration
      n arity p H G W P hp.2.1 hP
  have hprevious : OriginalRankGuardedRepresentative.Properties n arity p H G W :=
    ⟨transparentProperties n arity p H G W hp hH hG hW,
      actualOriginalRankGuardedRepresentativeLiteralFields p H G W,
      actualOriginalRankGuardedRepresentativeNativePreparation n arity p H G W hp hH hG hW,
      OriginalRankGuardedRepresentativeInternalProof.actualOriginalRankGuardedRepresentativeInternalRank
        p H G W,
      actualOriginalRankGuardedRepresentativeRetention n arity p H G W hp hH hG hW⟩
  have hminimum := actualOriginalTransparentMinimumInternalMinimum
    (OriginalTypedDecoder.target H G) Q
  have hretained := actualOriginalTransparentMinimumRetention n arity p H G W Q
    hp hH hG hW hQ
  have hproperties : OriginalTransparentMinimum.Properties n arity p H G W Q :=
    ⟨hprevious,hQ,actualOriginalTransparentMinimumLiteralFields p H G W Q,
      actualOriginalTransparentMinimumNativePreparation n arity p H G Q hp hH hG hQ,
      OriginalTransparentMinimumInternalReflexiveProof.actualOriginalTransparentMinimumInternalReflexive
        (OriginalTypedDecoder.target H G) Q,
      OriginalTransparentMinimumInternalScanProof.actualOriginalTransparentMinimumInternalScan _,
      hminimum,
      OriginalTransparentMinimumGuardedClassProof.guardedClassOfMinimum p H G W Q hminimum,
      hretained⟩
  have hfinal : OriginalFinalGuardedRank.Properties n arity s H G W :=
    ⟨hretained,actualOriginalFinalGuardedTraversalRank s H G W,
      actualOriginalFinalGuardedFoldRank s H G W,actualOriginalFinalGuardedObjectRank s H G W⟩
  exact ⟨hP,hproperties,
    OriginalActiveObservedClassProof.actualOriginalActiveObservedClassHit
      p H G W OriginalRawSyntaxTransport.variableRankPackedRaw P,
    OriginalActiveObservedClassCompletionProof.actualOriginalActiveObservedGuardCollapse p H G W P,
    OriginalActiveObservedMinimumInternalProof.actualOriginalActiveObservedMinimumInternalMinimum
      p H G W P,hfinal⟩

/-- Choose the existing original tuple and its class compiler once. Every
retained package, actual representative minimum and final rank law then belongs
to the same explicitly constructed tuple, before any window or runtime context. -/
theorem actualOriginalActiveObservedMinimumSelection :
    ActualOriginalActiveObservedMinimumSelection := by
  intro n arity
  obtain ⟨p,H,G,W,hprevious⟩ :=
    actualOriginalRankGuardedRepresentativeSelection n arity
  obtain ⟨P,hP⟩ :=
    OriginalTransparentMinimumClassSelectionProof.actualOriginalTransparentMinimumClassSelection n arity
  exact ⟨p,H,G,W,P,actualOriginalActiveObservedMinimumRetention n arity p H G W P
    hprevious.1.1 hprevious.1.2.1 hprevious.1.2.2.1 hprevious.1.2.2.2.1 hP⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedMinimumGlobalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedMinimumGlobalProof
