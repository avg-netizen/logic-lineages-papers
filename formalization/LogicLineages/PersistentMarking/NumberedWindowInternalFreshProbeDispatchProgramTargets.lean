module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramDefinitions
@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramTargets
open NumberedWindowInternalFreshProbeDispatchWindowTargets
open NumberedWindowInternalFreshProbeDispatchProgram
open NumberedWindowProbeCode (code NumericalTotal)
open NumberedWindowTypedProbe (typed probe)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowAddressApplication (graph)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

/-- Values of the pure ASTs on every input, including the zero cases. -/
def ExactDispatchControlEvaluation : Prop :=
  (∀ n k (xs : List.Vector Nat n), evaluate (literal n k) xs = k) ∧
  (∀ x, evaluate predOne (x ::ᵥ nil) = x.pred) ∧
  (∀ x y, evaluate compareNumbers (x ::ᵥ y ::ᵥ nil) = if x = y then 1 else 0) ∧
  (∀ n (f a b : Program n) xs,
    evaluate (chooseBranch f a b) xs = if evaluate f xs = 0 then evaluate a xs else evaluate b xs) ∧
  (∀ n (p q : Program n) xs,
    evaluate (bothOne p q) xs = if evaluate p xs = 1 ∧ evaluate q xs = 1 then 1 else 0)

def ExactProbeVerifyCalibration : Prop :=
  ∀ (s : Settings), NumericalTotal (typed s) (probe s) (graph s) →
    ∀ (l : Leaves), calibrated s l → ∀ (τ : ProbeTy) (q : Nat),
      evaluate (verify l τ) (q ::ᵥ nil) = (typed s (code τ) q).toNat

def ExactProbeDispatchCalibration : Prop :=
  ∀ (s : Settings) (W : List ProbeTy), ValidWindow s W →
    ∀ (l : Leaves), calibrated s l → ∀ (t q : Nat),
      evaluate (dispatch l W) (t ::ᵥ q ::ᵥ nil) = (typed s t q).toNat

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramTargets
