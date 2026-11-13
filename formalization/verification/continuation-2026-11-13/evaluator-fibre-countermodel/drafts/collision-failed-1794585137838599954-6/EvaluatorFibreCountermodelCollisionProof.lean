module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorFibreCountermodelObservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorFixedPointProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorFibreCountermodelCollisionProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
open NumberedLeastCodeRepresentative NumberedFiniteUniverse
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorFibreCountermodel EvaluatorFibreCountermodelObservationProof
theorem evaluatorEqual :
 evaluate evaluator (List.Vector.ofFn ![leftCode,parameter]) =
 evaluate evaluator (List.Vector.ofFn ![rightCode,parameter]) := by
 change OriginalHereditaryFiniteStability.value (OriginalHereditaryEvaluatorDefinitions.evaluator representative)
   contextCode ⟨[],leftTerm⟩ = OriginalHereditaryFiniteStability.value
   (OriginalHereditaryEvaluatorDefinitions.evaluator representative) contextCode ⟨[],rightTerm⟩
 rw [OriginalHereditaryEvaluatorFixedPointProof.fixedPoint representative 1 arity contextCode [] leftTerm,
     OriginalHereditaryEvaluatorFixedPointProof.fixedPoint representative 1 arity contextCode [] rightTerm]
 simp only [OriginalHereditaryFiniteStability.value]
 rw [OriginalHereditaryObservationLayerNativeProof.native,OriginalHereditaryObservationLayerNativeProof.native]
 rw [rootEqual representative,rootEqual evaluator,emptyRows evaluator leftCode,emptyRows evaluator rightCode]
theorem representativeDifferent :
 evaluate representative (List.Vector.ofFn ![leftCode,parameter]) ≠
 evaluate representative (List.Vector.ofFn ![rightCode,parameter]) := by
 change leftCode ≠ rightCode
 intro he
 simp [leftCode,rightCode,packedNumber,leftTerm,rightTerm,leftBase,rightBase,bottom,zero,
   NumberedAuxiliaryCoding.termCode,NumberedAuxiliaryCoding.argumentsCode,codeNumber,Nat.pair_eq_pair] at he
theorem actualCollision : EvaluatorFibreCountermodelTargets.ActualCollision :=
 ⟨emptyRows evaluator leftCode,emptyRows evaluator rightCode,evaluatorEqual,representativeDifferent⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorFibreCountermodelCollisionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorFibreCountermodelCollisionProof
