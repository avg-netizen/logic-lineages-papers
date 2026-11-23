module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelope
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptance (constantZero)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
  (evalBranch actualConjunctionEvaluation)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThan (constantOne ltTest)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof
  (exactLessThanEvaluation)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeTwo)
open NumberedWindowInternalAtomicRefinementNumericFieldsProof (sourceValue targetValue)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalAtomicRefinement (atSource atTarget)
open NumberedWindowInternalNeutralRankGuard

private theorem rankedBit (g : Program 1) (x w y : Nat) :
    evaluate (targetHasRank g) (x ::ᵥ w ::ᵥ y ::ᵥ nil) =
      if run g y = 0 then 0 else 1 := by
  rw [targetHasRank,evalBranch,targetValue]
  have zero : evaluate (constantZero 3) (x ::ᵥ w ::ᵥ y ::ᵥ nil) = 0 := rfl
  have one : evaluate (constantOne 3) (x ::ᵥ w ::ᵥ y ::ᵥ nil) = 1 := by
    simp [constantOne,constantZero,evaluate]
  rw [zero,one]

private theorem rankedLess (g : Program 1) (x w y : Nat) :
    evaluate (lowersRank g) (x ::ᵥ w ::ᵥ y ::ᵥ nil) =
      if run g y < run g x then 1 else 0 := by
  change evaluate (.composition ltTest (Fin.cons (atTarget g) (Fin.cons (atSource g) Fin.elim0)))
    (x ::ᵥ w ::ᵥ y ::ᵥ nil) = _
  rw [compositeTwo,targetValue,sourceValue]
  exact exactLessThanEvaluation (run g y) (run g x)

/-- Conservative on every original tape, provided the actual old
accepted positive rows give the two numerical neutral rank facts and
the old target scalar. Non-ranked rows keep the old code unchanged. -/
theorem exact_RankEvenNumeric (i g : Program 1) (r : Program 3)
    (old : Nat → Nat → Nat → Bool)
    (fit : ∀ x w y, evaluate r (x ::ᵥ w ::ᵥ y ::ᵥ nil) = (old x w y).toNat)
    (desc : ∀ x w y, old x w y = true → run g x ≠ 0 →
      run g y ≠ 0 ∧ run g y < run g x ∧ run i y = 1) :
    ∀ x w y, evaluate (rankEven i g r) (x ::ᵥ w ::ᵥ y ::ᵥ nil) = (old x w y).toNat := by
  intro x w y
  rw [rankEven,evalBranch,sourceValue]
  by_cases scalar : run g x = 0
  · rw [if_pos scalar,fit]
  · rw [if_neg scalar,actualConjunctionEvaluation,fit]
    cases hold : old x w y with
    | false => simp [hold]
    | true =>
      obtain ⟨pos,lt,carried⟩ := desc x w y hold scalar
      rw [actualConjunctionEvaluation,rankedBit,if_neg pos,actualConjunctionEvaluation,
        targetValue,carried,rankedLess,if_pos lt]
      rfl

/-- An independent all-input numerical check for the actual p refinement,
using exactly neutral-rank preservation and true destination scalar. -/
theorem exact_RankApplicationNumeric (i g : Program 1) (p : Program 3)
    (old : Nat → Nat → Nat → Bool)
    (fit : ∀ f u y, evaluate p (f ::ᵥ u ::ᵥ y ::ᵥ nil) = (old f u y).toNat)
    (holds : ∀ f u y, old f u y = true → run g f ≠ 0 → run g y ≠ 0 ∧ run i y = 1) :
    ∀ f u y, evaluate (rankApplication i g p) (f ::ᵥ u ::ᵥ y ::ᵥ nil) = (old f u y).toNat := by
  intro f u y
  rw [rankApplication,evalBranch,sourceValue]
  by_cases scalar : run g f = 0
  · rw [if_pos scalar,fit]
  · rw [if_neg scalar,actualConjunctionEvaluation,fit]
    cases hold : old f u y with
    | false => simp [hold]
    | true =>
      obtain ⟨pos,carried⟩ := holds f u y hold scalar
      rw [actualConjunctionEvaluation,rankedBit,if_neg pos,targetValue,carried]
      rfl

#print axioms exact_RankEvenNumeric
#print axioms exact_RankApplicationNumeric
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardNumericProof
