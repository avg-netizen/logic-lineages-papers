module

public import LogicLineages.PersistentMarking.NumberedWindowCheckerCoordinatesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterAddressProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedBaseProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneLiteralPriorTypedV2

open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowAddressAlgorithm (addressView)
open NumberedWindowCheckerCoordinates (domain)
open NumberedWindowCheckerCoordinatesProof (exact_ExactCoordinates)
open NumberedWindowInternalFreshProbeDispatchProgram (bothOne)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (bothEvaluation)
open NumberedWindowInternalFreshProbeParsedEmitterAddressProof (addressCoordinates)
open NumberedWindowInternalFreshProbeParsedTyped (requestedTypeTest)
open NumberedWindowInternalFreshProbeParsedTypedBaseProof (physicalTest)
open NumberedWindowInternalSparseApplicationFrontendTargets (ActualScalarCalibration)
open NumberedWindowScalarAlgorithm (Settings scalar)
open NumberedWindowTypedProbe (typed)

/-- The actual scalar and the original result-field test form the prior typing checker. -/
def priorTypedOf (i : Program 1) : Program 2 :=
  bothOne (domain i) requestedTypeTest

theorem exact_PriorTypedOfCalibration (s : Settings) (i : Program 1)
    (fit : ActualScalarCalibration s i) :
    ∀ t q, evaluate (priorTypedOf i) (t ::ᵥ q ::ᵥ nil) = (typed s t q).toNat := by
  intro t q
  rw [priorTypedOf, bothEvaluation, exact_ExactCoordinates.1, fit q, physicalTest]
  cases h : addressView q with
  | none =>
    have reject : scalar s q = false := by simp [scalar, h]
    simp [typed, h, reject]
  | some addr =>
    obtain ⟨ctx, ty, least⟩ := addr
    obtain ⟨_, _, _, result, _⟩ := addressCoordinates h
    rw [result]
    by_cases same : t = ty
    · subst t
      cases good : scalar s q <;> simp [typed, h, good]
    · have reverse : ty ≠ t := Ne.symm same
      have unequal : (ty == t) = false := by
        cases checked : (ty == t) with
        | false => rfl
        | true => exact False.elim (reverse (beq_iff_eq.mp checked))
      cases good : scalar s q <;> simp [typed, h, good, same, unequal]

#print axioms exact_PriorTypedOfCalibration

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneLiteralPriorTypedV2
