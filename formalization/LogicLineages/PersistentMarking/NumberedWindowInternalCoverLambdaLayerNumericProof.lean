module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLayerTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldNumericThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLayerNumericProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open ID1Completion.InternalListCodecEvaluationProof (consEvaluation)
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowFieldAlgorithm (packNode)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeTwo vectorTwo literalEvaluation)
open NumberedWindowInternalSparsePairEvaluationProof (consValue)
open NumberedWindowInternalCoverCartesianFoldTargets (flatMap)
open NumberedWindowInternalCoverCartesianFoldNumericThinProof (fixedCartesianFoldValue)
open NumberedWindowInternalCoverAuxApplicationsTargets (binary reorder)
open NumberedWindowInternalCoverNamedLeavesTargets (namedCode singletonLeaf typeBlock)
open NumberedWindowInternalCoverLambdaLayerTargets

private theorem reorderValue {m n : Nat} (P : Program m) (slots : Fin m → Fin n) (v : List.Vector Nat n) :
    evaluate (reorder P slots) v = evaluate P (List.Vector.ofFn fun i => v.get (slots i)) := rfl

private theorem cellValue (ty q : Nat) :
    evaluate (namedCode 2) (q ::ᵥ ty ::ᵥ nil) = packNode 2 [ty,q] := by
  simp only [namedCode,binary,compositeTwo,literalEvaluation]
  repeat rw [consValue]
  rfl

private theorem singleValue (ty q : Nat) :
    evaluate (singletonLeaf 2) (q ::ᵥ ty ::ᵥ nil) = numbersNumber [packNode 2 [ty,q]] := by
  rw [singletonLeaf,binary,compositeTwo,cellValue]
  exact consEvaluation _ 0

private theorem blockValue (ty : Nat) (children : List Nat) :
    evaluate (typeBlock 2) (ty ::ᵥ numbersNumber children ::ᵥ nil) =
      numbersNumber (children.map fun q => packNode 2 [ty,q]) := by
  rw [typeBlock,reorderValue,vectorTwo]
  change evaluate (flatMap (singletonLeaf 2)) (numbersNumber children ::ᵥ ty ::ᵥ nil) = _
  rw [fixedCartesianFoldValue (singletonLeaf 2) (fun q => [packNode 2 [ty,q]]) children (ty ::ᵥ nil)
    (fun q => singleValue ty q), List.map_eq_flatMap]

theorem exact_CoverLambdaLayerValue : ExactCoverLambdaLayerValue := by
  intro K children
  change evaluate (flatMap (typeBlock 2)) (numbersNumber K ::ᵥ numbersNumber children ::ᵥ nil) =
    numbersNumber (K.flatMap fun ty => children.map fun q => packNode 2 [ty,q])
  exact fixedCartesianFoldValue (typeBlock 2) _ K _ (fun ty => blockValue ty children)

#print axioms exact_CoverLambdaLayerValue

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLayerNumericProof
