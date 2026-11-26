module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.NativeProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldNumericProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalListMap (mapHead)
open ID1Completion.InternalRawListRecursionEvaluationProof (actualRawListRecursionEvaluation)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.NativeProof (appendEvaluation)
open NumberedMultisetNumeric (numbersNumber)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (vectorTwo)
open NumberedWindowInternalCoverCartesianFoldTargets

private theorem blockValue {k : Nat} (D : Program (k+1)) (a b : Nat) (params : List.Vector Nat k) :
    evaluate (mapHead D) (a ::ᵥ b ::ᵥ params) = evaluate D (a ::ᵥ params) := by
  apply congrArg (evaluate D)
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [List.Vector.get_ofFn,Fin.cons_succ,evaluate,List.Vector.get_cons_succ]

theorem fixedCartesianFoldValue {k : Nat} (D : Program (k+1)) (F : Nat → List Nat)
    (source : List Nat) (params : List.Vector Nat k)
    (calibrated : ∀ a, evaluate D (a ::ᵥ params) = numbersNumber (F a)) :
    evaluate (flatMap D) (numbersNumber source ::ᵥ params) = numbersNumber (source.flatMap F) := by
  rw [flatMap,actualRawListRecursionEvaluation,numbersRoundTrip]
  change List.foldr (fun a rest => evaluate (flatStep D) (a ::ᵥ rest ::ᵥ params)) 0 source = _
  induction source with
  | nil => rfl
  | cons a src ih =>
    rw [List.flatMap_cons,List.foldr_cons,ih]
    change evaluate append (List.Vector.ofFn ![
      evaluate (mapHead D) (a ::ᵥ numbersNumber (src.flatMap F) ::ᵥ params),
      numbersNumber (src.flatMap F)]) = _
    rw [blockValue,calibrated,appendEvaluation,numbersRoundTrip]
    rfl

theorem exact_CartesianFoldValue : ExactCartesianFoldValue := by
  intro k D F calibrated source params
  exact fixedCartesianFoldValue D (fun a => F a params) source params (fun a => calibrated a params)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldNumericProof
