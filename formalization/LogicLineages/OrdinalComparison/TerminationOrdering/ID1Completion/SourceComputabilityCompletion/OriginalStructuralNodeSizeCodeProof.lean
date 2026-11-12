module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeExecutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeBoundedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeCodeProof
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportSemanticProof (costFuelBound)
open OriginalStructuralNodeSizeSemanticProof OriginalStructuralNodeSizeExecutionProof
open OriginalStructuralNodeSizeBoundedProof OriginalStructuralNodeSizeTransitionEvaluationProof
open NumberedMultisetNumeric NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem rawSemantic (input : Nat) : OriginalStructuralNodeSize.rawValue input = semanticFold 0 0 input := by
  unfold OriginalStructuralNodeSize.rawValue
  rw [runAtSufficientCost 0 0 input (fuelValue input) (costFuelBound input)]
  simp [outputValue,encodeState,InternalApplicationResultStack.encodeState,numbersNumber,Nat.add_comm 1]

theorem semanticNodes {n : Nat} (q : Code (Fin n)) (d k : Nat) :
    semanticFold d k (codeNumber q) = OriginalStructuralNodeSize.nodeCount q := by
  induction q generalizing d k <;> rw [semanticEquation] <;>
    simp_all [codeNumber,arityValue,tagValue,payloadValue,firstValue,secondValue,
      OriginalStructuralNodeSize.rebuildValue,OriginalStructuralNodeSize.nodeCount]

theorem codeCalibration (n : Nat) (q : Code (Fin n)) :
    evaluate OriginalStructuralNodeSize.raw (List.Vector.ofFn ![codeNumber q]) = OriginalStructuralNodeSize.nodeCount q := by
  rw [rawEvaluation,rawSemantic]
  exact semanticNodes q 0 0

theorem actualNativeCalibration : OriginalStructuralNodeSizeTargets.NativeCalibration :=
  ⟨transitionCalibration,rawEvaluation,packedEvaluation,codeCalibration⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeCodeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeCodeProof
