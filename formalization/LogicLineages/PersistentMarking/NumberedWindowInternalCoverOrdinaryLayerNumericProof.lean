module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryLayerTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldNumericThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryLayerNumericProof
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
open NumberedWindowInternalCoverOrdinaryLayerTargets

private theorem reorderValue {m n : Nat} (P : Program m) (slots : Fin m → Fin n) (v : List.Vector Nat n) :
    evaluate (reorder P slots) v = evaluate P (List.Vector.ofFn fun i => v.get (slots i)) := rfl

private theorem cellValue (tag : Nat) (ty q : Nat) :
    evaluate (namedCode tag) (q ::ᵥ ty ::ᵥ nil) = packNode tag [ty,q] := by
  simp only [namedCode,binary,compositeTwo,literalEvaluation]
  repeat rw [consValue]
  rfl

private theorem singleValue (tag : Nat) (ty q : Nat) :
    evaluate (singletonLeaf tag) (q ::ᵥ ty ::ᵥ nil) = numbersNumber [packNode tag [ty,q]] := by
  rw [singletonLeaf,binary,compositeTwo,cellValue]
  exact consEvaluation _ 0

private theorem blockValue (tag : Nat) (ty : Nat) (children : List Nat) :
    evaluate (typeBlock tag) (ty ::ᵥ numbersNumber children ::ᵥ nil) =
      numbersNumber (children.map fun q => packNode tag [ty,q]) := by
  rw [typeBlock,reorderValue,vectorTwo]
  change evaluate (flatMap (singletonLeaf tag)) (numbersNumber children ::ᵥ ty ::ᵥ nil) = _
  rw [fixedCartesianFoldValue (singletonLeaf tag) (fun q => [packNode tag [ty,q]]) children (ty ::ᵥ nil)
    (fun q => singleValue tag ty q), List.map_eq_flatMap]

theorem taggedLayerValue (tag : Nat) : ExactTaggedLayerValue tag := by
  intro K children
  change evaluate (flatMap (typeBlock tag)) (numbersNumber K ::ᵥ numbersNumber children ::ᵥ nil) =
    numbersNumber (K.flatMap fun ty => children.map fun q => packNode tag [ty,q])
  exact fixedCartesianFoldValue (typeBlock tag) _ K _ (fun ty => blockValue tag ty children)

theorem exact_CoverOrdinaryLayerValue : ExactCoverOrdinaryLayerValue :=
  taggedLayerValue 4

#print axioms exact_CoverOrdinaryLayerValue

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryLayerNumericProof
