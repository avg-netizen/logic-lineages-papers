module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativeTypedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarIdentityProgramsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativeSourceProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative
open NumberedNumericDecoding NumberedNumericCarrier
open InternalOriginalUniformDescentSelection (Data Calibrated)
open UniformCertificateCompletion OriginalLambdaTraversalSelection
open OriginalLambdaTraversalNativeCalibrationSupportProof OriginalLambdaTraversalNativeTypedProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The active guard sees exactly the acyclic leaf supplier's validator.
Its representative field is irrelevant to this literal identity. -/
theorem activeLeaf (rawData : Data) (window : Program 1) :
    OriginalFunctionNeutrality.active (transparentData rawData) window =
      InternalAcceptance.conjunction (BottomRepresentative.windowAt window)
        (InternalOriginalUniformDescentSelection.validity (leafData rawData window)) := by
  rw [OriginalApplicationSidecarIdentityProgramsProof.activeOriginal]
  exact congrArg (InternalAcceptance.conjunction (BottomRepresentative.windowAt window))
    (OriginalApplicationSidecarIdentityProgramsProof.sameValidity
      (transparentData rawData) window).symm

/-- Actual original source decoding supplies the typed term only INSIDE
the active proof. The raw parameter and context code are unchanged. -/
theorem canonicalAtSource (n : Nat) (arity : Fin n → Nat) (rawData : Data) (window : Program 1)
    (hc : Calibrated n arity rawData) (hw : Path.windowCalibrated n window)
    (value parameter : Nat) (ctx : OrdinaryArithmeticQuotient.Context n) (Gamma : List Ty)
    (hctx : Encodable.decode (Nat.unpair parameter).1 = some ctx)
    (hg : Encodable.encode Gamma = (Nat.unpair parameter).2)
    (hS : SubtypeClosed (fun tau => tau ∈ ctx.1.2))
    (hs : InternalOriginalStepGuard.sourceValidityValue n arity ctx.1.1 ctx.1.2 Gamma value = 1) :
    evaluate (canonical rawData window) (List.Vector.ofFn ![value,parameter]) =
      InternalQuotientEdgeChecker.targetRepresentativeValue n arity ctx.1.1 ctx.1.2 Gamma value := by
  cases hd : decodeUniverse n arity ctx.1.1 ctx.1.2 Gamma value with
  | none => simp [InternalOriginalStepGuard.sourceValidityValue,rawCarrierTest,hd] at hs
  | some q =>
    obtain ⟨hnum,hq⟩ :=
      (NumberedNumericCarrierProof.numericUniverseDecode n arity ctx.1.1 ctx.1.2 Gamma value q).mp hd
    rcases q with ⟨tau,q⟩
    rw [← hnum,InternalRepresentativeFoldCalibrationSupportProof.targetOnPacked]
    exact canonicalAtTyped n arity rawData window hc hw parameter ctx Gamma hctx hg hS tau q hq

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativeSourceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativeSourceProof
