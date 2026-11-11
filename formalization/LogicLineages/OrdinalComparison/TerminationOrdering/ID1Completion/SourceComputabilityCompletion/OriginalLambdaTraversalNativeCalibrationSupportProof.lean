module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityRefinementProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativeCalibrationSupportProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative
open InternalOriginalUniformDescentSelection (Data Calibrated)
open InternalOriginalUniformParameterLeaves (parameterObject)
open UniformCertificateCompletion OriginalLambdaTraversalSelection
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem transparentCalibrated (n : Nat) (arity : Fin n → Nat) (rawData : Data)
    (hc : Calibrated n arity rawData) : Calibrated n arity (transparentData rawData) :=
  (OriginalTransparentLambdaValidityRefinementProof.actualOriginalTransparentRefinementCalibration
    n arity rawData hc).2.2.2

/-- The prior selected leaf is calibrated independently, before C exists.
Only already accepted original refinement/calibration suppliers are used. -/
theorem leafDataCalibrated (n : Nat) (arity : Fin n → Nat) (rawData : Data)
    (window : Program 1) (hc : Calibrated n arity rawData)
    (hw : Path.windowCalibrated n window) : Calibrated n arity (leafData rawData window) := by
  have ht := transparentCalibrated n arity rawData hc
  have hs := (OriginalApplicationSidecarCalibrationProof.actualOriginalApplicationSidecarRefinementEquality
    n arity (transparentData rawData) window ht hw).2
  exact OriginalApplicationSidecarCalibrationProof.originalDataCalibrated n arity
    (OriginalApplicationSidecar.baseData (transparentData rawData) window) window hs hw

/-- Choose the actual supplied Gamma through its original Object decoder.
The outer context remains the caller's RAW code, never encode(decode(code)). -/
theorem decodedAtGamma (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : Calibrated n arity data) (parameter : Nat)
    (ctx : OrdinaryArithmeticQuotient.Context n) (Gamma : List Ty)
    (hctx : Encodable.decode (Nat.unpair parameter).1 = some ctx)
    (hg : Encodable.encode Gamma = (Nat.unpair parameter).2)
    (hS : SubtypeClosed (fun tau => tau ∈ ctx.1.2)) :
    DecodedSourceCalibration.DecodedCalibration n arity data parameter ctx Gamma := by
  obtain ⟨Gamma',hd⟩ := DecodedSourceCalibrationProof.actualDecodedCompositeCalibration
    n arity data hc parameter ctx hctx hS
  have ho := OriginalTransparentLambdaValidityParameterProof.objectAtGamma 0 parameter Gamma hg
  have he : Gamma' = Gamma :=
    congrArg Prod.fst (Option.some.inj ((hd.objectSlice 0).symm.trans ho))
  cases he
  exact hd

/-- Native leaf calibration on a genuine typed input needs no source-window
membership of that term. Closedness belongs only to the decoded context. -/
theorem leafAtTyped (n : Nat) (arity : Fin n → Nat) (rawData : Data) (window : Program 1)
    (hc : Calibrated n arity rawData) (hw : Path.windowCalibrated n window)
    (parameter : Nat) (ctx : OrdinaryArithmeticQuotient.Context n) (Gamma : List Ty)
    (hctx : Encodable.decode (Nat.unpair parameter).1 = some ctx)
    (hg : Encodable.encode Gamma = (Nat.unpair parameter).2)
    (hS : SubtypeClosed (fun tau => tau ∈ ctx.1.2))
    (tau : Ty) (q : AuxTerm (Fin n) arity Gamma tau) :
    evaluate (leaf rawData window) (List.Vector.ofFn ![packedNumber ⟨tau,q⟩,parameter]) =
      representativeCode ctx.1.1 ctx.1.2 ⟨tau,q⟩ := by
  have hd := decodedAtGamma n arity (leafData rawData window)
    (leafDataCalibrated n arity rawData window hc hw) parameter ctx Gamma hctx hg hS
  exact (hd.representative (packedNumber ⟨tau,q⟩)).trans
    (InternalRepresentativeFoldCalibrationSupportProof.targetOnPacked
      n arity ctx.1.1 ctx.1.2 Gamma ⟨tau,q⟩)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativeCalibrationSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativeCalibrationSupportProof
