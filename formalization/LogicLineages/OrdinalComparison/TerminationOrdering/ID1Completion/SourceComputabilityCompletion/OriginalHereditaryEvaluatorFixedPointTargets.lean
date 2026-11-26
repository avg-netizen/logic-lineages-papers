module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextPrefixNativeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorFixedPointTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedMultisetNumeric
open OriginalHereditaryEvaluatorDefinitions OriginalHereditaryFiniteStability
/-- Native fixed-point equation at actual typed inputs only. No internal
reflection, allraw guarantee or source-equivalence completeness. -/
def FixedPoint : Prop := ∀ R n (arity : Fin n → Nat) c (Gamma : List Ty)
 (q : Packed (Fin n) arity Gamma),
 value (evaluator R) c ⟨Gamma,q⟩ =
 value (OriginalHereditaryObservationLayer.layer R (evaluator R)) c ⟨Gamma,q⟩
/-- Equality of actual evaluator outputs transports through every valid
context deletion. The explicit typed prefix/suffix encode an arbitrary cutoff. -/
def DeletionEquality : Prop := ∀ R n (arity : Fin n → Nat) c (binders tail : List Ty) (sigma : Ty)
 (q r : Packed (Fin n) arity (binders ++ sigma::tail)),
 value (evaluator R) c ⟨binders ++ sigma::tail,q⟩ = value (evaluator R) c ⟨binders ++ sigma::tail,r⟩ →
 value (evaluator R) c ⟨binders ++ tail,
   NumberedPrimarySubstitution.substitutePacked (OriginalRawSyntaxTransport.prefixErasure binders tail sigma) q⟩ =
 value (evaluator R) c ⟨binders ++ tail,
   NumberedPrimarySubstitution.substitutePacked (OriginalRawSyntaxTransport.prefixErasure binders tail sigma) r⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorFixedPointTargets
