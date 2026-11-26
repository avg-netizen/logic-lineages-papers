module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldNumericThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsNumericProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open ID1Completion.InternalListCodecEvaluationProof (consEvaluation)
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowCoverAlgorithm (cells)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeTwo vectorTwo)
open NumberedWindowInternalSparsePairEvaluationProof (consValue)
open NumberedWindowInternalCoverCartesianFoldTargets (flatMap)
open NumberedWindowInternalCoverCartesianFoldNumericThinProof (fixedCartesianFoldValue)
open NumberedWindowInternalCoverAuxApplicationsTargets (binary reorder)
open NumberedWindowInternalCoverArgumentCellsTargets

private theorem reorderValue {m n : Nat} (P : Program m) (slots : Fin m → Fin n) (v : List.Vector Nat n) :
    evaluate (reorder P slots) v = evaluate P (List.Vector.ofFn fun i => v.get (slots i)) := rfl

private theorem cellValue (q a : Nat) :
    evaluate cellSingle (a ::ᵥ q ::ᵥ nil) = numbersNumber [pair q a + 1] := by
  rw [cellSingle,binary,compositeTwo,reorderValue,vectorTwo]
  change evaluate ID1Completion.InternalListCodec.consCode
    (evaluate NumberedWindowInternalSparsePair.fieldCons (q ::ᵥ a ::ᵥ nil) ::ᵥ 0 ::ᵥ nil) = _
  rw [consValue]
  exact consEvaluation _ 0

private theorem blockValue (q : Nat) (args : List Nat) :
    evaluate cellBlock (q ::ᵥ numbersNumber args ::ᵥ nil) =
      numbersNumber (args.map fun a => pair q a + 1) := by
  rw [cellBlock,reorderValue,vectorTwo]
  change evaluate (flatMap cellSingle) (numbersNumber args ::ᵥ q ::ᵥ nil) = _
  rw [fixedCartesianFoldValue cellSingle (fun a => [pair q a + 1]) args (q ::ᵥ nil)
    (fun a => cellValue q a), List.map_eq_flatMap]

theorem exact_CoverArgumentCellsValue : ExactCoverArgumentCellsValue := by
  intro terms args
  rw [cellsAt,binary,compositeTwo]
  change evaluate ID1Completion.InternalListCodec.consCode
    (0 ::ᵥ evaluate (flatMap cellBlock) (numbersNumber terms ::ᵥ numbersNumber args ::ᵥ nil) ::ᵥ nil) = _
  rw [fixedCartesianFoldValue cellBlock _ terms (numbersNumber args ::ᵥ nil) (fun q => blockValue q args)]
  exact consEvaluation _ _

#print axioms exact_CoverArgumentCellsValue

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsNumericProof
