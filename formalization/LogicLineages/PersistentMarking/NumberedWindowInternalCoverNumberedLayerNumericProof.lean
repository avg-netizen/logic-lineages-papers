module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldNumericThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsNumericTapeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerNumericProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open ID1Completion.InternalListCodecEvaluationProof (consEvaluation)
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowFieldAlgorithm (packNode)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeTwo literalEvaluation)
open NumberedWindowInternalSparseDirectedRoundsNumericTapeProof (vectorFour vectorFive)
open NumberedWindowInternalSparsePairEvaluationProof (consValue)
open NumberedWindowInternalCoverCartesianFoldTargets (flatMap)
open NumberedWindowInternalCoverCartesianFoldNumericThinProof (fixedCartesianFoldValue)
open NumberedWindowInternalCoverAuxApplicationsTargets (binary reorder)
open NumberedWindowInternalCoverNumberedLayerTargets

private theorem reorderValue {m n : Nat} (P : Program m) (slots : Fin m → Fin n) (v : List.Vector Nat n) :
    evaluate (reorder P slots) v = evaluate P (List.Vector.ofFn fun i => v.get (slots i)) := rfl

private theorem nodeValue (h ty k l r : Nat) :
    evaluate numberedCode (r ::ᵥ h ::ᵥ ty ::ᵥ k ::ᵥ l ::ᵥ nil) = packNode 5 [h,ty,k,l,r] := by
  simp only [numberedCode,binary,compositeTwo,literalEvaluation]
  repeat rw [consValue]
  rfl

private theorem singleValue (h ty k l r : Nat) :
    evaluate singletonNumbered (r ::ᵥ h ::ᵥ ty ::ᵥ k ::ᵥ l ::ᵥ nil) =
      numbersNumber [packNode 5 [h,ty,k,l,r]] := by
  rw [singletonNumbered,binary,compositeTwo,nodeValue]
  exact consEvaluation _ 0

private theorem prefixValue (args : List Nat) (h ty k l : Nat) :
    evaluate prefixBlock (l ::ᵥ numbersNumber args ::ᵥ h ::ᵥ ty ::ᵥ k ::ᵥ nil) =
      numbersNumber (args.map fun r => packNode 5 [h,ty,k,l,r]) := by
  rw [prefixBlock,reorderValue,vectorFive]
  change evaluate (flatMap singletonNumbered) (numbersNumber args ::ᵥ h ::ᵥ ty ::ᵥ k ::ᵥ l ::ᵥ nil) = _
  rw [fixedCartesianFoldValue singletonNumbered (fun r => [packNode 5 [h,ty,k,l,r]]) args
    (h ::ᵥ ty ::ᵥ k ::ᵥ l ::ᵥ nil) (fun r => singleValue h ty k l r), List.map_eq_flatMap]

private theorem idValue (args : List Nat) (h ty k : Nat) :
    evaluate idBlock (k ::ᵥ numbersNumber args ::ᵥ h ::ᵥ ty ::ᵥ nil) =
      numbersNumber (args.flatMap fun l => args.map fun r => packNode 5 [h,ty,k,l,r]) := by
  rw [idBlock,reorderValue,vectorFive]
  change evaluate (flatMap prefixBlock)
    (numbersNumber args ::ᵥ numbersNumber args ::ᵥ h ::ᵥ ty ::ᵥ k ::ᵥ nil) = _
  exact fixedCartesianFoldValue prefixBlock _ args _ (fun l => prefixValue args h ty k l)

private theorem typeValue (ids args : List Nat) (h ty : Nat) :
    evaluate typeBlock (ty ::ᵥ numbersNumber ids ::ᵥ numbersNumber args ::ᵥ h ::ᵥ nil) =
      numbersNumber (ids.flatMap fun k => args.flatMap fun l => args.map fun r => packNode 5 [h,ty,k,l,r]) := by
  rw [typeBlock,reorderValue,vectorFour]
  change evaluate (flatMap idBlock) (numbersNumber ids ::ᵥ numbersNumber args ::ᵥ h ::ᵥ ty ::ᵥ nil) = _
  exact fixedCartesianFoldValue idBlock _ ids _ (fun k => idValue args h ty k)

private theorem headValue (K ids args : List Nat) (h : Nat) :
    evaluate headBlock (h ::ᵥ numbersNumber K ::ᵥ numbersNumber ids ::ᵥ numbersNumber args ::ᵥ nil) =
      numbersNumber (K.flatMap fun ty => ids.flatMap fun k => args.flatMap fun l =>
        args.map fun r => packNode 5 [h,ty,k,l,r]) := by
  rw [headBlock,reorderValue,vectorFour]
  change evaluate (flatMap typeBlock) (numbersNumber K ::ᵥ numbersNumber ids ::ᵥ numbersNumber args ::ᵥ h ::ᵥ nil) = _
  exact fixedCartesianFoldValue typeBlock _ K _ (fun ty => typeValue ids args h ty)

theorem exact_CoverNumberedLayerValue : ExactCoverNumberedLayerValue := by
  intro H K ids args
  exact fixedCartesianFoldValue headBlock _ H _ (headValue K ids args)

#print axioms exact_CoverNumberedLayerValue

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerNumericProof
