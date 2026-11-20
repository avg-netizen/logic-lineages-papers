module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedNumericTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectTargets
public import LogicLineages.PersistentMarking.NumberedWindowConcreteGuardedGraphTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedSelectionTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowFunctionalGraphTargets NumberedWindowGuardedGraphTargets
open NumberedWindowFormulaCalibrationTargets NumberedWindowPresentationCheckers
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalAccessibilityTargets (Rules)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalProbeTargets (TypedProbeTotal)
open NumberedWindowTypedProbe (typed probe)
open NumberedWindowInternalFreshProbeParsedTyped
open NumberedWindowInternalFreshProbeParsedTypedObjectTargets (OpenLiteralParsed)

/-- The original #596 actual concrete checker tuple with this one
physical parsed a and refined h. No numeral-program equivalence
transports old derivations. This remains conditional on the genuine
window interface; it is not the blocked mixed fixed-S,K endpoint. -/
def ExactConcreteParsedTypedTuple : Prop :=
  ∀ (xs : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
    ∃ (i j : Program 1) (r d : Program 3) (v : Inputs),
      Evaluates (checks xs s) i j r d ∧
      Interprets (checks xs s) (data i j r d) ∧ Rules (data i j r d) ∧
      CalibratedInputs s v ∧ UniqueResult v.applicationGuard ∧
      InputGuards i j r d v.applicationGuard ∧
      (∀ q, evaluate (chosenA v) (q ::ᵥ nil) = Encodable.encode (probe s q)) ∧
      (∀ t q, evaluate (chosenH v W) (t ::ᵥ q ::ᵥ nil) = (typed s t q).toNat) ∧
      (∀ c, TypedProbeTotal (data i j r d) v.applicationGuard (chosenH v W) (chosenA v) c) ∧
      OpenLiteralParsed v W

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedSelectionTargets
