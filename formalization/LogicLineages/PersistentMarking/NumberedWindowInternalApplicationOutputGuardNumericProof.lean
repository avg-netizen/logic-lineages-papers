module

public import LogicLineages.PersistentMarking.NumberedWindowInternalApplicationOutputGuardTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalApplicationOutputGuardNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open NumberedWindowInternalApplicationOutputGuardTargets
open NumberedWindowGuardedGraphTargets (atSlot)

theorem exact_ApplicationOutputGuardEvaluation (i : Program 1) (p : Program 3) (f u y : Nat) :
    evaluate (outputGuard i p) (f ::ᵥ u ::ᵥ y ::ᵥ nil) =
      (if evaluate p (f ::ᵥ u ::ᵥ y ::ᵥ nil) = 1 ∧ evaluate i (y ::ᵥ nil) = 1 then 1 else 0) := by
  rw [outputGuard, actualConjunctionEvaluation] <;> rfl

/-- Sound calibration for a chosen output test precisely when accepted
numeric outputs already satisfy it; no unchecked converse at object level. -/
theorem exact_ApplicationOutputGuardCalibration (i : Program 1) (p : Program 3) (g : Nat → Nat → Nat → Bool)
    (fit : ∀ f u y, evaluate p (f ::ᵥ u ::ᵥ y ::ᵥ nil) = (g f u y).toNat)
    (closed : ∀ f u y, g f u y = true → evaluate i (y ::ᵥ nil) = 1) :
    ∀ f u y, evaluate (outputGuard i p) (f ::ᵥ u ::ᵥ y ::ᵥ nil) = (g f u y).toNat := by
  intro f u y
  rw [exact_ApplicationOutputGuardEvaluation, fit]
  cases h : g f u y with
  | false => simp
  | true => simp [closed f u y h]

#print axioms exact_ApplicationOutputGuardEvaluation
#print axioms exact_ApplicationOutputGuardCalibration
end LogicLineages.PersistentMarking.NumberedWindowInternalApplicationOutputGuardNumericProof
