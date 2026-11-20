import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalNumericTargets
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeDispatchProgram
open NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets (sourceWindow)
open NumberedWindowProbeCode (code)
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowTypedProbe (typed probe)
open NumberedWindowAddressApplication (graph)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

def ExactOriginalVerifyCalibration : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    ∀ (l : Leaves), calibrated (fixed S K) l → ∀ (τ : ProbeTy) (q : Nat),
      evaluate (verify l τ) (q ::ᵥ nil) = (typed (fixed S K) (code τ) q).toNat

def ExactOriginalDispatchCalibration : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    ∀ (l : Leaves), calibrated (fixed S K) l → ∀ (t q : Nat),
      evaluate (dispatch l (sourceWindow K)) (t ::ᵥ q ::ᵥ nil) = (typed (fixed S K) t q).toNat

/-- Select the very same a and p and both original computational leaves.
Retain the literal dispatch AST for independent object-packet integration. -/
def ExactOriginalSelectedCalibration : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    ∀ (p : Program 3) (a : Program 1),
      (∀ q u v, evaluate p (q ::ᵥ u ::ᵥ v ::ᵥ nil) = (graph (fixed S K) q u v).toNat) →
      (∀ q, evaluate a (q ::ᵥ nil) = Encodable.encode (probe (fixed S K) q)) →
      ∃ l : Leaves, l.applicationGuard = p ∧ l.fresh = a ∧ calibrated (fixed S K) l ∧
        ∀ t q, evaluate (dispatch l (sourceWindow K)) (t ::ᵥ q ::ᵥ nil) =
          (typed (fixed S K) t q).toNat

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalNumericTargets
