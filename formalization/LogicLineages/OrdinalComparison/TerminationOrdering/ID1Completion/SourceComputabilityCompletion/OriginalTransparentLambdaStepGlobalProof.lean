module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepGlobalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepWrapperProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumGlobalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativePreparationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepGlobalProof
open UniformCertificateCompletion OriginalTransparentLambdaStepGlobal
open OriginalTransparentLambdaStepGlobalTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Combine original source with the fully wrapped original step, before
normalization; all untouched calibration fields are literally inherited. -/
theorem preparedCalibrated (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    GlobalSourcePackage.InputsCalibrated n arity (prepared p) := by
  let q : GlobalSourcePackage.Inputs :=
    { p with oldStep := (OriginalHereditaryLambdaGlobal.priorFinal p).oldStep }
  have hi := OriginalHereditaryLambdaGlobalPreparationProof.priorFinalCalibrated n arity p hp
  have hq : GlobalSourcePackage.InputsCalibrated n arity q :=
    ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,hi.2.2.2.2.1,hp.2.2.2.2.2⟩
  exact OriginalTransparentLambdaStepNativeProof.actualOriginalTransparentLambdaStepCalibration n arity q hq

/-- Rebuild the exact minimum, rank guard, transparent decoders, and ONE
variable refinement in the retained package's literal order. -/
theorem refinedCalibrated (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (hp : GlobalSourcePackage.InputsCalibrated n arity p)
    (hH : OriginalTypedDecoder.HeadSignatureCalibrated n arity H)
    (hG : OriginalVariableLeaves.ContextGuardCalibrated n G)
    (hW : OriginalUniverseDecoder.HeadWindowCalibrated n arity W)
    (hP : OriginalTransparentMinimum.ClassTestCalibrated n arity P) :
    GlobalSourcePackage.InputsCalibrated n arity (refined p H G W P) := by
  let q := prepared p
  have hq := preparedCalibrated n arity p hp
  let K := OriginalActiveClassKernel.classTest q H G W P
  have hK := OriginalActiveClassKernelCalibrationProof.actualOriginalActiveClassKernelCalibration
    n arity q H G W P hq hH hG hW hP
  let Q := OriginalActiveObservedClass.classTest q H G W OriginalRawSyntaxTransport.variableRankPackedRaw K
  have hQ : OriginalTransparentMinimum.ClassTestCalibrated n arity Q :=
    OriginalActiveObservedCalibrationProof.actualOriginalActiveObservedRankCalibration
      n arity q H G W K hq.2.1 hK
  let m := OriginalTransparentMinimum.minimumInputs H G Q q
  have hm := (OriginalTransparentMinimumNativeProof.actualOriginalTransparentMinimumNativePreparation
    n arity q H G Q hq hH hG hQ).2
  have hg := (OriginalRankGuardedRepresentativeNativeProof.actualOriginalRankGuardedRepresentativeNativePreparation
    n arity m H G W hm hH hG hW).2
  have hs := (OriginalTransparentDecoderSelectionCalibrationProof.actualOriginalTransparentDecoderCalibration
    n arity (OriginalRankGuardedRepresentative.guardedInputs H G W m) H G W hg hH hG hW).1
  exact OriginalVariableLeavesRefinementProof.refinedInputsCalibration n arity G
    (selected p H G W P) hG hs

theorem nativePreparation (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (hp : GlobalSourcePackage.InputsCalibrated n arity p)
    (hH : OriginalTypedDecoder.HeadSignatureCalibrated n arity H)
    (hG : OriginalVariableLeaves.ContextGuardCalibrated n G)
    (hW : OriginalUniverseDecoder.HeadWindowCalibrated n arity W)
    (hP : OriginalTransparentMinimum.ClassTestCalibrated n arity P) :
    NativePreparation n arity p H G W P := by
  have hq := preparedCalibrated n arity p hp
  have hr := refinedCalibrated n arity p H G W P hp hH hG hW hP
  have hf := (OriginalLambdaTraversalNativePreparationProof.actualOriginalLambdaTraversalNativePreparation
    n arity (refined p H G W P) hr).2.1
  refine ⟨hq,hr,hf,?_⟩
  intro v
  exact ⟨(hq.2.2.2.2.1 v).trans (hp.2.2.2.2.1 v).symm,
    (hr.2.2.2.2.1 v).trans (hp.2.2.2.2.1 v).symm,
    (hf.2.2.2.2.1 v).trans (hp.2.2.2.2.1 v).symm⟩

/-- Every subsequent preparation changes only base fields or adds exactly
the original hereditary wrappers, so this is an AST identity, not calibration. -/
theorem actualOriginalTransparentLambdaStepGlobalLiteralLeaf :
    ActualOriginalTransparentLambdaStepGlobalLiteralLeaf := by
  intro p H G W P
  rfl

theorem actualOriginalTransparentLambdaStepGlobalIntroduction :
    ActualOriginalTransparentLambdaStepGlobalIntroduction := by
  intro p H G W P
  unfold FinalIntroduction
  rw [actualOriginalTransparentLambdaStepGlobalLiteralLeaf p H G W P]
  exact OriginalTransparentLambdaStepWrapperProof.actualOriginalTransparentLambdaClosedLeafIntroduction
    p.base.oldSource (OriginalHereditaryLambdaGlobal.priorFinal p).oldStep
    (OriginalHereditaryLambdaGlobal.endpoint
      (OriginalLambdaTraversalSelection.prepareInputs (refined p H G W P)))
    (refined p H G W P).window

theorem actualOriginalTransparentLambdaStepGlobalRetention :
    ActualOriginalTransparentLambdaStepGlobalRetention := by
  intro n arity p H G W P hp hH hG hW hP
  exact ⟨nativePreparation n arity p H G W P hp hH hG hW hP,
    OriginalActiveKernelMinimumGlobalProof.actualOriginalActiveKernelMinimumRetention
      n arity (prepared p) H G W P (preparedCalibrated n arity p hp) hH hG hW hP,
    actualOriginalTransparentLambdaStepGlobalLiteralLeaf p H G W P,
    actualOriginalTransparentLambdaStepGlobalIntroduction p H G W P⟩

theorem actualOriginalTransparentLambdaStepGlobalSelection :
    ActualOriginalTransparentLambdaStepGlobalSelection := by
  intro n arity
  obtain ⟨p,H,G,W,hprevious⟩ :=
    OriginalRankGuardedRepresentativeGlobalProof.actualOriginalRankGuardedRepresentativeSelection n arity
  obtain ⟨P,hP⟩ := OriginalTransparentMinimumClassSelectionProof.actualOriginalTransparentMinimumClassSelection n arity
  exact ⟨p,H,G,W,P,actualOriginalTransparentLambdaStepGlobalRetention n arity p H G W P
    hprevious.1.1 hprevious.1.2.1 hprevious.1.2.2.1 hprevious.1.2.2.2.1 hP⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepGlobalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepGlobalProof
