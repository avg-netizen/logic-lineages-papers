module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedNumericTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterAddressProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedBaseProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowAddressAlgorithm (addressView)
open NumberedWindowScalarAlgorithm (scalar)
open NumberedWindowTypedProbe (typed)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalFreshProbeParsedEmitter (rawResult)
open NumberedWindowInternalFreshProbeParsedEmitterAddressProof (addressCoordinates)
open NumberedWindowInternalFreshProbeDispatchProgram (compareNumbers)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof
  (compositeOne compositeTwo compareEvaluation bothEvaluation)
open NumberedWindowInternalFreshProbeParsedTyped
open NumberedWindowInternalFreshProbeParsedTypedNumericTargets

private theorem resultAtValue (t q : Nat) :
    evaluate resultAtSecond (t ::ᵥ q ::ᵥ nil) = run rawResult q := by
  rw [resultAtSecond,compositeOne] <;> rfl

theorem physicalTest : ExactPhysicalTypeTest := by
  intro t q
  rw [requestedTypeTest,compositeTwo,resultAtValue]
  change evaluate compareNumbers (t ::ᵥ run rawResult q ::ᵥ nil) = _
  exact compareEvaluation t (run rawResult q)

theorem baseCalibration : ExactBaseWithResultCalibration := by
  intro s prior old t q
  rw [baseWithResult,bothEvaluation,old,physicalTest]
  cases ht : typed s t q with
  | false => simp [ht]
  | true =>
    cases hv : addressView q with
    | none => simp [typed,hv] at ht
    | some addr =>
      rcases addr with ⟨Γ,r,k⟩
      have same : scalar s q = true ∧ r = t := by
        simpa [typed,hv] using ht
      obtain ⟨_,_,_,result,_⟩ := addressCoordinates hv
      have requested : run rawResult q = t := result.trans same.2
      simp [ht,requested]

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedBaseProof
