module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedSelectionTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSelectionTargets
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
open NumberedWindowInternalFreshProbeAlignmentTargets (AlignedCarriersAt)

/-- Same actual #596 checker tuple and #642 p/a/h, with given-u aligned
existence and scalar carriers added without changing any code. The
real valid-window premise remains explicit. -/
def ExactConcreteParsedFreshCarrierTuple : Prop :=
  ∀ (xs : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
    ∃ (i j : Program 1) (r d : Program 3) (v : Inputs),
      Evaluates (checks xs s) i j r d ∧
      Interprets (checks xs s) (data i j r d) ∧ Rules (data i j r d) ∧
      CalibratedInputs s v ∧ UniqueResult v.applicationGuard ∧
      InputGuards i j r d v.applicationGuard ∧
      (∀ q, evaluate (chosenA v) (q ::ᵥ nil) = Encodable.encode (probe s q)) ∧
      (∀ t q, evaluate (chosenH v W) (t ::ᵥ q ::ᵥ nil) = (typed s t q).toNat) ∧
      (∀ c, TypedProbeTotal (data i j r d) v.applicationGuard (chosenH v W) (chosenA v) c) ∧
      OpenLiteralParsed v W ∧
      ∀ c, AlignedCarriersAt (data i j r d) v.applicationGuard (chosenH v W) (chosenA v) c

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSelectionTargets
