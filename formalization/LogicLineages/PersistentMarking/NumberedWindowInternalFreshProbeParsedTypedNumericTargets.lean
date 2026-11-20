module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedNumericTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedEmitter (rawResult)
open NumberedWindowInternalFreshProbeParsedTyped
open NumberedWindowTypedProbe (typed probe)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelope (run)

def ExactPhysicalTypeTest : Prop :=
  ∀ t q, evaluate requestedTypeTest (t ::ᵥ q ::ᵥ nil) =
    if t = run rawResult q then 1 else 0

/-- Failures, malformed source codes and unrequested types behave
exactly as in the original all-input numerical typed test. -/
def ExactBaseWithResultCalibration : Prop :=
  ∀ (s : Settings) (priorTyped : Program 2),
    (∀ t q, evaluate priorTyped (t ::ᵥ q ::ᵥ nil) = (typed s t q).toNat) →
    ∀ t q, evaluate (baseWithResult priorTyped) (t ::ᵥ q ::ᵥ nil) = (typed s t q).toNat

/-- The very same chosen a/h used in later object targets preserve the
original all-code relations on the actual fixed finite window interface. -/
def ExactParsedTypedCalibration : Prop :=
  ∀ (s : Settings) (W : List ProbeTy), ValidWindow s W →
    ∀ i : Inputs, CalibratedInputs s i →
      (∀ q, evaluate (chosenA i) (q ::ᵥ nil) = Encodable.encode (probe s q)) ∧
      (∀ t q, evaluate (chosenH i W) (t ::ᵥ q ::ᵥ nil) = (typed s t q).toNat)

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedNumericTargets
