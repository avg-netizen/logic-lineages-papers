module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalObjectCoherenceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativePreparationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterSelectionCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformCanonicalResultFoldEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryWeakeningProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalObjectCoherenceCalibrationProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative
open UniformCertificateCompletion OriginalFinalObjectCoherence OriginalRawObjectTransport
open NumberedPrimaryWeakening NumberedPrimarySubstitution
open OriginalContextExtensionCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Calibrate exactly OuterSelection.data at the already-final input tuple.
No application-sidecar refinement or replacement tuple is inserted. -/
theorem finalDataCalibrated (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    InternalOriginalUniformDescentSelection.Calibrated n arity
      (OriginalLambdaTraversalSelection.finalData p) := by
  have hfinal :=
    (OriginalLambdaTraversalNativePreparationProof.actualOriginalLambdaTraversalNativePreparation
      n arity p hp).2.1
  have hpre := OuterSelectionCalibrationProof.preCalibrated n arity
    (OriginalLambdaTraversalSelection.finalInputs p).base hfinal.1
    (OriginalLambdaTraversalSelection.finalInputs p).window hfinal.2.1
  exact InternalOriginalUniformContextMembershipEvaluationProof.actualOriginalUniformNormalizedMembershipCalibration
    n arity _ hpre

/-- The wrapper is merely the original Object encoding of the literal
SAME final fold's calibrated representative. This is native equality only. -/
theorem canonicalOnPacked (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun tau => tau ∈ S)) (q : Packed (Fin n) arity Gamma) :
    canonicalObject p (OrdinaryArithmeticQuotient.contextCode symbols S table)
      (ContextUniform.objectCode Gamma (packedNumber q)) =
    ContextUniform.objectCode Gamma (representativeCode symbols S q) := by
  have hfold :=
    (InternalOriginalUniformCanonicalResultFoldEvaluationProof.actualOriginalUniformCanonicalResultFoldCalibration
      n arity (OriginalLambdaTraversalSelection.finalData p)
      (finalDataCalibrated n arity p hp) symbols S Gamma table hS (packedNumber q)).1
  have htarget := InternalRepresentativeFoldCalibrationSupportProof.targetOnPacked
    n arity symbols S Gamma q
  simpa only [canonicalObject,objectEncoding,Nat.unpair_pair,
    InternalOriginalUniformParameterLeaves.parameterCode] using
    congrArg (Nat.pair (Encodable.encode Gamma)) (hfold.trans htarget)

theorem shiftObjectOnPacked (n : Nat) (arity : Fin n → Nat)
    (Gamma : List Ty) (sigma : Ty) (q : Packed (Fin n) arity Gamma) :
    evaluate shiftObjectRaw (List.Vector.ofFn ![typeNumber sigma,
      ContextUniform.objectCode Gamma (packedNumber q)]) =
    ContextUniform.objectCode (sigma :: Gamma)
      (packedNumber (renamePacked (Renaming.weaken Gamma sigma) q)) := by
  obtain ⟨tau,q⟩ := q
  exact (OriginalRawObjectTransportNativeProof.actualRawObjectTypedCalibration
    n arity Gamma sigma tau).1 q

theorem eraseObjectOnPacked (n : Nat) (arity : Fin n → Nat)
    (Gamma : List Ty) (sigma : Ty) (q : Packed (Fin n) arity (sigma :: Gamma)) :
    evaluate eraseObjectRaw (List.Vector.ofFn ![
      ContextUniform.objectCode (sigma :: Gamma) (packedNumber q)]) =
    ContextUniform.objectCode Gamma
      (packedNumber (substitutePacked (singleSubstitution (.bottom sigma)) q)) := by
  obtain ⟨tau,q⟩ := q
  exact (OriginalRawObjectTransportNativeProof.actualRawObjectTypedCalibration
    n arity Gamma sigma tau).2.1 q

theorem rankObjectOnPacked (n : Nat) (arity : Fin n → Nat)
    (Gamma : List Ty) (q : Packed (Fin n) arity Gamma) :
    evaluate variableRankObjectRaw (List.Vector.ofFn ![
      ContextUniform.objectCode Gamma (packedNumber q)]) =
    NumberedVariableCount.packedVariableCount q := by
  obtain ⟨tau,q⟩ := q
  exact (OriginalRawObjectTransportNativeProof.actualRawObjectTypedCalibration
    n arity Gamma Ty.ground tau).2.2 q

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalObjectCoherenceCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalObjectCoherenceCalibrationProof
