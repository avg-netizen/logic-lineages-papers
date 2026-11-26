module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyPutTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorExactProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyTypedProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedMultisetNumeric
open NumberedFiniteUniverse NumberedWindowEquivalence
open OriginalHereditaryEvaluatorDefinitions OriginalHereditaryFiniteStability
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Native typed-domain compatibility ONLY. The internal row proofs may not
reflect this calibration result into arithmetic derivations. -/
theorem typedKeyIff (n : Nat) (arity : Fin n → Nat)
 (data : InternalOriginalUniformDescentSelection.Data)
 (hc : InternalOriginalUniformDescentSelection.Calibrated n arity data)
 (c : Nat) (ctx : OrdinaryArithmeticQuotient.Context n)
 (hctx : Encodable.decode c = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
 (Gamma : List Ty) (q r : Packed (Fin n) arity Gamma)
 (hq : InUniverse ctx.1.1 ctx.1.2 q.2) (hr : InUniverse ctx.1.1 ctx.1.2 r.2) :
 (evaluate (evaluator data.oldRepresentative) (List.Vector.ofFn ![packedNumber q,Nat.pair c (typesNumber Gamma)]) =
  evaluate (evaluator data.oldRepresentative) (List.Vector.ofFn ![packedNumber r,Nat.pair c (typesNumber Gamma)])) ↔
 (evaluate data.oldRepresentative (List.Vector.ofFn ![packedNumber q,Nat.pair c (typesNumber Gamma)]) =
  evaluate data.oldRepresentative (List.Vector.ofFn ![packedNumber r,Nat.pair c (typesNumber Gamma)])) := by
 rw [OriginalRootObservationActualProof.representativeAtTyped n arity data hc c ctx hctx Gamma q,
   OriginalRootObservationActualProof.representativeAtTyped n arity data hc c ctx hctx Gamma r]
 change (value (evaluator data.oldRepresentative) c ⟨Gamma,q⟩ =
   value (evaluator data.oldRepresentative) c ⟨Gamma,r⟩) ↔ _
 rw [OriginalHereditaryEvaluatorExactProof.exactPrimary n arity data hc c ctx hctx hclosed Gamma q r hq hr]
 exact (NumberedLeastCodeRepresentativeProof.representativeEquality n arity ctx.1.1 ctx.1.2 hclosed Gamma q r hq hr).symm
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyTypedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyTypedProof
