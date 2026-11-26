module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationActualTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationSignatureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralClassKeyCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalRetentionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativeRefinementProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderReconstructionLocalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationActualProof
open UniformCertificateCompletion OriginalRootObservation
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Decoded-context calibration works for every typed term, not only source members. -/
theorem representativeAtTyped (n : Nat) (arity : Fin n → Nat)
    (data : InternalOriginalUniformDescentSelection.Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (c : Nat) (ctx : OrdinaryArithmeticQuotient.Context n)
    (hctx : Encodable.decode c = some ctx) (Gamma : List Ty)
    (q : Packed (Fin n) arity Gamma) :
    evaluate data.oldRepresentative
      (List.Vector.ofFn ![packedNumber q,Nat.pair c (typesNumber Gamma)]) =
      representativeCode ctx.1.1 ctx.1.2 q := by
  have hg : Encodable.encode Gamma = (Nat.unpair (Nat.pair c (typesNumber Gamma))).2 := by
    rw [Nat.unpair_pair]
    exact OriginalTypedDecoderReconstructionLocalProof.contextNumber Gamma
  have hd : Encodable.decode (Nat.unpair (Nat.pair c (typesNumber Gamma))).1 = some ctx := by
    simpa only [Nat.unpair_pair] using hctx
  have ho := fun value => OriginalTransparentLambdaValidityParameterProof.objectAtGamma
    value (Nat.pair c (typesNumber Gamma)) Gamma hg
  exact ((BottomRepresentativeEvaluationProof.decodedLeafSlice n arity data hc
    (Nat.pair c (typesNumber Gamma)) ctx hd Gamma ho (packedNumber q)).2.2.1).trans
      (InternalRepresentativeFoldCalibrationSupportProof.targetOnPacked n arity ctx.1.1 ctx.1.2 Gamma q)

theorem actualStructuralKey : OriginalRootObservationActualTargets.StructuralKey := by
  intro n arity p H G W hp hH hG hW c ctx hctx Gamma q
  have hs := (OriginalStructuralClassKeyCalibrationProof.actualOriginalStructuralClassKeyCalibration
    n arity p H G W hp hH hG hW).2
  apply OriginalRootObservationSignatureProof.actualSignatureCalibration
  intro Delta t
  exact representativeAtTyped n arity
    (OriginalStructuralClassKeyDefinitions.inputs p H G W).base hs.1 c ctx hctx Delta t

theorem actualGuardedRepresentative : OriginalRootObservationActualTargets.GuardedRepresentative := by
  intro n arity p H G W P hp hH hG hW hP c ctx hctx Gamma q
  let r := OriginalAllPositionStructuralTraversalDefinitions.refined p H G W P
  have hr : GlobalSourcePackage.InputsCalibrated n arity r :=
    (OriginalAllPositionStructuralTraversalRetentionProof.actualRetention
      n arity p H G W P hp hH hG hW hP).1.2.2
  apply OriginalRootObservationSignatureProof.actualSignatureCalibration
  intro Delta t
  exact (OriginalLambdaTraversalNativeRefinementProof.representativeUnchanged
    n arity r.base r.window hr.1 hr.2.1
      (List.Vector.ofFn ![packedNumber t,Nat.pair c (typesNumber Delta)])).trans
    (representativeAtTyped n arity r.base hr.1 c ctx hctx Delta t)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationActualProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationActualProof
