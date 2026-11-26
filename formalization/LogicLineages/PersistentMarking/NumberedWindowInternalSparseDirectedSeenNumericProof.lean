module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion
open GorbowVerifierNormalization (normalize)
open InternalAcceptance (constantZero)
open InternalAcceptanceCalibrationProof (evalBranch evalNormalize)
open InternalEqualityTest (equalityTest)
open InternalEqualityTestEvaluationProof (vectorTwo exactEqualityEvaluation)
open InternalRawListRecursion (listRec)
open InternalRawListRecursionEvaluationProof (actualRawListRecursionEvaluation)
open NumberedMultisetNumeric (decodeNumbers)
open NumberedWindowInternalSparseDirectedSeen
open NumberedWindowInternalSparseDirectedSeenTargets

private theorem ofFour (f : Fin 4 → Nat) :
    List.Vector.ofFn f = f 0 ::ᵥ f 1 ::ᵥ f 2 ::ᵥ f 3 ::ᵥ nil := by
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_
    (fun l => Fin.cases ?_ (fun x => Fin.elim0 x) l) k) j) i <;> simp <;> rfl

private theorem eqValue (w prev ctx ty v : Nat) :
    evaluate headEq (w ::ᵥ prev ::ᵥ ctx ::ᵥ ty ::ᵥ v ::ᵥ nil) =
      (if w = v then 1 else 0) := by
  change evaluate equalityTest (List.Vector.ofFn ![w,v]) = _
  rw [vectorTwo]
  exact exactEqualityEvaluation w v

private theorem edgeValue (E : Program 4) (w prev ctx ty v : Nat) :
    evaluate (edgeCall E) (w ::ᵥ prev ::ᵥ ctx ::ᵥ ty ::ᵥ v ::ᵥ nil) =
      evaluate E (List.Vector.ofFn (edgeTape ctx ty w v)) := by
  let xs := w ::ᵥ prev ::ᵥ ctx ::ᵥ ty ::ᵥ v ::ᵥ nil
  change evaluate E (List.Vector.ofFn (fun i : Fin 4 => evaluate
    ((![.projection 2,.projection 3,.projection 0,.projection 4] : Fin 4 → Program 5) i) xs)) = _
  simp only [ofFour] <;> rfl

private theorem stepValue (E : Program 4) (w prev ctx ty v : Nat) :
    evaluate (scanStep E) (w ::ᵥ prev ::ᵥ ctx ::ᵥ ty ::ᵥ v ::ᵥ nil) =
      if w = v then 1 else if evaluate E (List.Vector.ofFn (edgeTape ctx ty w v)) = 1 then 1 else prev := by
  let xs := w ::ᵥ prev ::ᵥ ctx ::ᵥ ty ::ᵥ v ::ᵥ nil
  have headValue : evaluate (normalize headEq) xs = if w = v then 1 else 0 := by
    rw [evalNormalize,eqValue]
    by_cases same : w = v <;> simp [same]
  change evaluate (scanStep E) xs = _
  by_cases same : w = v
  · have control : evaluate (normalize headEq) xs = 1 := by
      simpa only [if_pos same] using headValue
    rw [scanStep,evalBranch,control,if_neg Nat.one_ne_zero,if_pos same] <;> rfl
  · have control : evaluate (normalize headEq) xs = 0 := by
      simpa only [if_neg same] using headValue
    rw [scanStep,evalBranch,control,if_pos rfl,evalBranch,evalNormalize,edgeValue]
    by_cases linked : evaluate E (List.Vector.ofFn (edgeTape ctx ty w v)) = 1 <;>
      simp only [same,linked,ite_true,ite_false,Nat.one_ne_zero] <;> rfl

private theorem foldBit (E : Program 4) (pool : List Nat) (ctx ty v : Nat) :
    pool.foldr (fun w prev => evaluate (scanStep E) (w ::ᵥ prev ::ᵥ ctx ::ᵥ ty ::ᵥ v ::ᵥ nil)) 0 =
      (pool.any (fun w => (w == v) || decide (evaluate E (List.Vector.ofFn (edgeTape ctx ty w v)) = 1))).toNat := by
  induction pool with
  | nil => rfl
  | cons w tail ih =>
    rw [List.foldr_cons,ih,stepValue,List.any_cons]
    by_cases same : w = v
    · simp [same]
    · have miss : (w == v) = false := Bool.eq_false_iff.mpr (fun hit => same (eq_of_beq hit))
      by_cases linked : evaluate E (List.Vector.ofFn (edgeTape ctx ty w v)) = 1 <;>
        simp [same,miss,linked]

theorem allInput : ExactAllInputDirectedSeen := by
  intro E seen ctx ty v
  rw [ofFour]
  change evaluate (listRec (constantZero 3) (scanStep E)) (seen ::ᵥ ctx ::ᵥ ty ::ᵥ v ::ᵥ nil) = _
  rw [actualRawListRecursionEvaluation 3 (constantZero 3) (scanStep E) (ctx ::ᵥ ty ::ᵥ v ::ᵥ nil) seen]
  cases decoded : decodeNumbers seen with
  | none => rfl
  | some pool => exact foldBit E pool ctx ty v

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenNumericProof
