module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorExactTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorFixedPointProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorExactProjectionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedMultisetNumeric
open NumberedFiniteUniverse NumberedWindowEquivalence NumberedHereditaryView
open OriginalHereditaryEvaluatorDefinitions OriginalHereditaryFiniteStability
theorem baseRootEquality (R : Program 2) {n : Nat} {arity : Fin n → Nat} (c : Nat)
 {Gamma : List Ty} (q r : Packed (Fin n) arity Gamma)
 (h : value (evaluator R) c ⟨Gamma,q⟩ = value (evaluator R) c ⟨Gamma,r⟩) :
 value (OriginalRootObservation.rootObservation R) c ⟨Gamma,q⟩ =
 value (OriginalRootObservation.rootObservation R) c ⟨Gamma,r⟩ := by
 rw [OriginalHereditaryEvaluatorFixedPointProof.fixedPoint R n arity c Gamma q,
   OriginalHereditaryEvaluatorFixedPointProof.fixedPoint R n arity c Gamma r] at h
 simp only [value] at h ⊢
 rw [OriginalHereditaryObservationLayerNativeProof.native,
   OriginalHereditaryObservationLayerNativeProof.native] at h
 have hh := congrArg (fun x => (Nat.unpair x).1) h
 simpa only [Nat.unpair_pair] using hh

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorExactProjectionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorExactProjectionProof
