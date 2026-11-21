module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeNumericFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero)
open InternalAcceptanceCalibrationProof (evalBranch)
open InternalEqualityTest (predecessor equalityTest)
open InternalEqualityTestEvaluationProof
  (vectorOne vectorTwo vectorThree exactPredecessorEvaluation exactEqualityEvaluation)
open NumberedWindowFieldAlgorithm (pack packNode)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowAtomicPositiveTargets (packedAddress)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeTwo literalEvaluation)
open NumberedWindowInternalAtomicApplicationShape (addressEmitter)
open NumberedWindowInternalAtomicApplicationShapeNumericFieldsProof (exactEmitters)
open NumberedWindowInternalSparsePathAdvanceTargets (packedLeast encodeState ActualLeastCalibration)
open NumberedWindowInternalSparseApplicationOutputCore
open NumberedWindowInternalSparseApplicationOutputCoreTargets

private abbrev tape (ctx dom cod fn arg y : Nat) : List.Vector Nat 6 :=
  ctx ::ᵥ dom ::ᵥ cod ::ᵥ fn ::ᵥ arg ::ᵥ y ::ᵥ nil

private theorem zeroValue (v : List.Vector Nat 6) : evaluate (constantZero 6) v = 0 := rfl

private theorem consValue (p q : Program 6) (v : List.Vector Nat 6) :
    evaluate (consOf p q) v = pair (evaluate p v) (evaluate q v) + 1 := by
  rw [consOf,compositeTwo]
  exact NumberedWindowInternalSparsePairEvaluationProof.consValue _ _

private theorem seedValue (ctx dom cod fn arg y : Nat) :
    evaluate seed (tape ctx dom cod fn arg y) = packNode 6 [dom,cod,fn,arg] := by
  let v := tape ctx dom cod fn arg y
  have h₁ : evaluate (.projection (1 : Fin 6)) v = dom := rfl
  have h₂ : evaluate (.projection (2 : Fin 6)) v = cod := rfl
  have h₃ : evaluate (.projection (3 : Fin 6)) v = fn := rfl
  have h₄ : evaluate (.projection (4 : Fin 6)) v = arg := rfl
  change evaluate seed v = _
  simp only [seed,consValue,h₁,h₂,h₃,h₄,zeroValue,literalEvaluation,packNode,pack]

private theorem leastValue (least : Program 3) (ctx dom cod fn arg y : Nat) :
    evaluate (selectedLeast least) (tape ctx dom cod fn arg y) =
      evaluate least (ctx ::ᵥ cod ::ᵥ packNode 6 [dom,cod,fn,arg] ::ᵥ nil) := by
  let v := tape ctx dom cod fn arg y
  change evaluate least (List.Vector.ofFn (fun i : Fin 3 =>
    evaluate ((![.projection 0,.projection 2,seed] : Fin 3 → Program 6) i) v)) = _
  rw [vectorThree]
  change evaluate least (ctx ::ᵥ cod ::ᵥ evaluate seed v ::ᵥ nil) = _
  rw [seedValue]

private theorem classValue (least : Program 3) (v : List.Vector Nat 6) :
    evaluate (selectedClass least) v = (evaluate (selectedLeast least) v).pred := by
  change evaluate predecessor (List.Vector.ofFn (fun _ : Fin 1 => evaluate (selectedLeast least) v)) = _
  rw [vectorOne,exactPredecessorEvaluation]

private theorem addressValue (least : Program 3) (ctx dom cod fn arg y : Nat) :
    evaluate (outputAddress least) (tape ctx dom cod fn arg y) =
      packNode 3 [ctx,cod,evaluate (selectedClass least) (tape ctx dom cod fn arg y)] := by
  let v := tape ctx dom cod fn arg y
  change evaluate addressEmitter (List.Vector.ofFn (fun i : Fin 3 =>
    evaluate ((![.projection 0,.projection 2,selectedClass least] : Fin 3 → Program 6) i) v)) = _
  rw [vectorThree]
  change evaluate addressEmitter (ctx ::ᵥ cod ::ᵥ evaluate (selectedClass least) v ::ᵥ nil) =
    packedAddress ctx cod (evaluate (selectedClass least) v)
  exact exactEmitters.1 ctx cod (evaluate (selectedClass least) v)

private theorem compareValue (least : Program 3) (ctx dom cod fn arg y : Nat) :
    evaluate (compareOutput least) (tape ctx dom cod fn arg y) =
      if y = evaluate (outputAddress least) (tape ctx dom cod fn arg y) then 1 else 0 := by
  let v := tape ctx dom cod fn arg y
  change evaluate equalityTest (List.Vector.ofFn (fun i : Fin 2 =>
    evaluate ((![.projection 5,outputAddress least] : Fin 2 → Program 6) i) v)) = _
  rw [vectorTwo]
  exact exactEqualityEvaluation y (evaluate (outputAddress least) v)

theorem allInput : ExactAllInputApplicationOutputCore := by
  intro s least actual ctx dom cod fn arg y
  let v := tape ctx dom cod fn arg y
  let chosen := packedLeast s ctx cod (packNode 6 [dom,cod,fn,arg])
  have h : evaluate (selectedLeast least) v = encodeState chosen :=
    (leastValue least ctx dom cod fn arg y).trans (actual ctx cod (packNode 6 [dom,cod,fn,arg]))
  change evaluate (outputCore least) v = ((originalOutput s ctx dom cod fn arg == some y).toNat)
  rw [outputCore,evalBranch,zeroValue,compareValue,addressValue,classValue,h]
  change (if encodeState chosen = 0 then 0 else
      if y = packNode 3 [ctx,cod,(encodeState chosen).pred] then 1 else 0) =
    ((chosen.map (fun k => packNode 3 [ctx,cod,k]) == some y).toNat)
  cases chosen with
  | none => rfl
  | some k =>
    by_cases picked : y = packNode 3 [ctx,cod,k]
    · simp [encodeState,picked]
    · have opposite : packNode 3 [ctx,cod,k] ≠ y := Ne.symm picked
      have notEqualBit : (packNode 3 [ctx,cod,k] == y) = false :=
        Bool.eq_false_iff.mpr (fun checked => opposite (eq_of_beq checked))
      simp [encodeState,picked,notEqualBit]

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreNumericProof
