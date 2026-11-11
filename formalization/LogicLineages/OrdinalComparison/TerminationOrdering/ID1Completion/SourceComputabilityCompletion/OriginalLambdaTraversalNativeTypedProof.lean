module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativeSemanticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativeCalibrationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalCompletionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalBoundedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativeTypedProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative
open NumberedFiniteUniverse
open InternalOriginalUniformDescentSelection (Data Calibrated)
open UniformCertificateCompletion OriginalLambdaTraversalSelection
open OriginalLambdaTraversalNativeCalibrationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Calibrate the actual bounded C at a typed universe member, using its
independent run calibration and native semantics. The raw context coordinate
and the actual encoded Gamma remain unchanged, including at nested lambdas. -/
theorem canonicalAtTyped (n : Nat) (arity : Fin n → Nat) (rawData : Data) (window : Program 1)
    (hc : Calibrated n arity rawData) (hw : Path.windowCalibrated n window)
    (parameter : Nat) (ctx : OrdinaryArithmeticQuotient.Context n) (Gamma : List Ty)
    (hctx : Encodable.decode (Nat.unpair parameter).1 = some ctx)
    (hg : Encodable.encode Gamma = (Nat.unpair parameter).2)
    (hS : SubtypeClosed (fun tau => tau ∈ ctx.1.2))
    (tau : Ty) (q : AuxTerm (Fin n) arity Gamma tau) (hq : InUniverse ctx.1.1 ctx.1.2 q) :
    evaluate (canonical rawData window) (List.Vector.ofFn ![packedNumber ⟨tau,q⟩,parameter]) =
      representativeCode ctx.1.1 ctx.1.2 ⟨tau,q⟩ := by
  rw [OriginalLambdaTraversalSelection.canonical, OriginalLambdaTraversalBoundedProof.foldEvaluation,
    OriginalLambdaTraversalCompletionProof.foldSemantic]
  apply OriginalLambdaTraversalNativeSemanticProof.semanticTyped n arity ctx.1.1 ctx.1.2 hS
    _ (Nat.unpair parameter).1 ?_ Gamma tau q parameter rfl hg hq
  intro Delta rho r parameter' hcontext hg'
  have hctx' : Encodable.decode (Nat.unpair parameter').1 = some ctx := by
    rw [hcontext]
    exact hctx
  exact leafAtTyped n arity rawData window hc hw parameter' ctx Delta hctx' hg' hS rho r

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativeTypedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalNativeTypedProof
