module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldNumericThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesNumericProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open ID1Completion.InternalListCodecEvaluationProof (consEvaluation)
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowFieldAlgorithm (packNode)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeTwo literalEvaluation)
open NumberedWindowInternalSparsePairEvaluationProof (consValue)
open NumberedWindowInternalCoverCartesianFoldTargets (flatMap)
open NumberedWindowInternalCoverCartesianFoldNumericThinProof (fixedCartesianFoldValue)
open NumberedWindowInternalCoverAuxApplicationsTargets (binary)
open NumberedWindowInternalCoverTypeLeavesTargets

private theorem nodeValue (ty : Nat) :
    evaluate typeLeafCode (ty ::ᵥ nil) = packNode 3 [ty] := by
  simp only [typeLeafCode,binary,compositeTwo,literalEvaluation]
  repeat rw [consValue]
  rfl

private theorem singletonValue (ty : Nat) :
    evaluate typeLeafSingleton (ty ::ᵥ nil) = numbersNumber [packNode 3 [ty]] := by
  rw [typeLeafSingleton,binary,compositeTwo,nodeValue]
  exact consEvaluation _ 0

theorem exact_CoverTypeLeavesValue : ExactCoverTypeLeavesValue := by
  intro K
  unfold typeLeaves
  rw [fixedCartesianFoldValue typeLeafSingleton (fun ty => [packNode 3 [ty]]) K nil singletonValue,
    List.map_eq_flatMap]

#print axioms exact_CoverTypeLeavesValue

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesNumericProof
