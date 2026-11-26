module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeCorrectnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpectedReturnSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFuelProgramProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySettledObserverProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderReconstructionLocalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedAuxiliaryCoding
open OriginalHereditaryEvaluatorDefinitions OriginalHereditaryExpectedReturnSupportProof
open OriginalHereditaryRuntimeSemanticDefinitions

theorem jobTyped {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
 (q : Packed (Fin n) arity Gamma) : OriginalHereditaryTypedJobDefinitions.Typed arity (termJob q) :=
 OriginalHereditaryTypedJobDefinitions.CoreTyped.term q.2

theorem nativeCalibration : OriginalHereditaryEvaluatorTargets.NativeCalibration := by
 intro R n arity c Gamma q
 have hj : evaluate job (ofFn ![packedNumber q,Nat.pair c (typesNumber Gamma)]) =
   OriginalHereditaryRuntimeWork.jobNumber c (termJob q) := by
   rw [OriginalHereditaryEvaluatorEvaluationProof.jobEvaluation]
   simp only [packedNumber,Nat.unpair_pair,OriginalHereditaryRuntimeWork.jobNumber,
     OriginalHereditaryAnnotatedExpansion.jobNumber,OriginalHereditaryExpansion.jobNumber,termJob,OriginalTypedDecoderReconstructionLocalProof.contextNumber]
 have hi : evaluate initial (ofFn ![packedNumber q,Nat.pair c (typesNumber Gamma)]) =
   state c [.visit (termJob q)] [] := by
   rw [OriginalHereditaryEvaluatorEvaluationProof.initialEvaluation,hj]
   rfl
 obtain ⟨v,hv,he⟩ := OriginalHereditaryRuntimeCorrectnessProof.budgetExecution R n arity c (termJob q) [] (jobTyped q)
 have hh := termValue R c q v hv
 subst v
 rw [OriginalHereditaryEvaluatorEvaluationProof.evaluation,hj,hi,
   OriginalHereditaryFuelProgramProof.runtimeCalibration,he]
 simp only [state,OriginalHereditaryVisitScheduler.stateNumber,List.map_nil,
   NumberedMultisetNumeric.numbersNumber,Nat.unpair_pair,Nat.add_sub_cancel_left]

theorem sourcePreserves : OriginalHereditaryEvaluatorTargets.SourcePreserves := by
 intro R n arity symbols S c hS hR Gamma q r hq hr hqr
 rw [nativeCalibration,nativeCalibration]
 exact OriginalHereditarySettledObserverProof.uniformity R n arity symbols S c hS hR Gamma q r hq hr hqr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorProof
