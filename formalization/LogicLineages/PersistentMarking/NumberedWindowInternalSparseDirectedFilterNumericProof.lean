module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenNumericChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterNumericProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open ID1Completion
open InternalAcceptance (constantZero)
open InternalAcceptanceCalibrationProof (evalBranch evalNormalize)
open InternalEqualityTestEvaluationProof (vectorTwo)
open InternalListCodec (consCode)
open InternalListCodecEvaluationProof (consEvaluation)
open InternalRawListRecursion (listRec)
open InternalRawListRecursionEvaluationProof (actualRawListRecursionEvaluation)
open NumberedMultisetNumeric (decodeNumbers numbersNumber)
open NumberedWindowInternalSparseDirectedSeen (scan scanTape edgeTape)
open NumberedWindowInternalSparseDirectedSeenNumericChecks (exact_AllInputDirectedSeen)
open NumberedWindowInternalSparseDirectedFilter
open NumberedWindowInternalSparseDirectedFilterTargets

private theorem ofFour (f : Fin 4 → Nat) :
    List.Vector.ofFn f = f 0 ::ᵥ f 1 ::ᵥ f 2 ::ᵥ f 3 ::ᵥ nil := by
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_
    (fun l => Fin.cases ?_ (fun x => Fin.elim0 x) l) k) j) i <;> simp <;> rfl

private def keep (E : Program 4) (seen ctx ty v : Nat) : Bool :=
  ((decodeNumbers seen).getD []).any (fun w =>
    (w == v) || decide (evaluate E (List.Vector.ofFn (edgeTape ctx ty w v)) = 1))

private theorem queryTape (E : Program 4) (v rest seen ctx ty : Nat) :
    evaluate (scanHead E) (v ::ᵥ rest ::ᵥ seen ::ᵥ ctx ::ᵥ ty ::ᵥ nil) =
      evaluate (scan E) (List.Vector.ofFn (scanTape seen ctx ty v)) := by
  let xs := v ::ᵥ rest ::ᵥ seen ::ᵥ ctx ::ᵥ ty ::ᵥ nil
  change evaluate (scan E) (List.Vector.ofFn (fun i : Fin 4 => evaluate
    ((![.projection 2,.projection 3,.projection 4,.projection 0] : Fin 4 → Program 5) i) xs)) = _
  simp only [ofFour] <;> rfl

private theorem queryBit (E : Program 4) (v rest seen ctx ty : Nat) :
    evaluate (scanHead E) (v ::ᵥ rest ::ᵥ seen ::ᵥ ctx ::ᵥ ty ::ᵥ nil) =
      (keep E seen ctx ty v).toNat := by
  rw [queryTape, exact_AllInputDirectedSeen E seen ctx ty v]
  unfold keep
  cases decodeNumbers seen <;> rfl

private theorem emitted (v rest seen ctx ty : Nat) :
    evaluate prependHead (v ::ᵥ rest ::ᵥ seen ::ᵥ ctx ::ᵥ ty ::ᵥ nil) =
      1 + Nat.pair v rest := by
  change evaluate consCode (List.Vector.ofFn ![v,rest]) = _
  rw [vectorTwo]
  exact consEvaluation v rest

private theorem stepValue (E : Program 4) (v rest seen ctx ty : Nat) :
    evaluate (filterStep E) (v ::ᵥ rest ::ᵥ seen ::ᵥ ctx ::ᵥ ty ::ᵥ nil) =
      if keep E seen ctx ty v then 1 + Nat.pair v rest else rest := by
  rw [filterStep,evalBranch,evalNormalize,queryBit]
  cases keep E seen ctx ty v with
  | false =>
    simp only [Bool.toNat_false,Nat.zero_ne_one,ite_false,ite_true,Bool.false_eq_true] <;> rfl
  | true =>
    simp only [Bool.toNat_true,ite_true,Nat.one_ne_zero,ite_false]
    exact emitted v rest seen ctx ty

/-- Literal ordered filter result, not just equivalent membership or a set. -/
private theorem foldValue (E : Program 4) (pool : List Nat) (seen ctx ty : Nat) :
    pool.foldr (fun v r => evaluate (filterStep E) (v ::ᵥ r ::ᵥ seen ::ᵥ ctx ::ᵥ ty ::ᵥ nil)) 0 =
      numbersNumber (pool.filter (keep E seen ctx ty)) := by
  induction pool with
  | nil => rfl
  | cons v tail ih =>
    rw [List.foldr_cons,ih,stepValue,List.filter_cons]
    cases kept : keep E seen ctx ty v <;>
      simp only [kept,Bool.false_eq_true,ite_false,ite_true,numbersNumber]

theorem allInput : ExactAllInputDirectedFilter := by
  intro E vertices seen ctx ty
  rw [ofFour]
  change evaluate (listRec (constantZero 3) (filterStep E))
    (vertices ::ᵥ seen ::ᵥ ctx ::ᵥ ty ::ᵥ nil) = _
  rw [actualRawListRecursionEvaluation 3 (constantZero 3) (filterStep E) (seen ::ᵥ ctx ::ᵥ ty ::ᵥ nil) vertices]
  unfold NumberedWindowClassAlgorithm.advance
  exact foldValue E ((decodeNumbers vertices).getD []) seen ctx ty

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedFilterNumericProof
