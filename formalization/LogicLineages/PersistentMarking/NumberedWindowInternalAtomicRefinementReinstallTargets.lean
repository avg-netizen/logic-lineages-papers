module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSelectionTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementReinstallTargets
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
open NumberedWindowInternalAtomicRefinement (refined)

/-- Exactly the retained #644 literal tuple payload at a specified r and
specified original leaves. No rule transports between source bodies. -/
def TupleAt (xs : Entries) (s : Settings) (W : List ProbeTy)
    (i j : Program 1) (r d : Program 3) (v : Inputs) : Prop :=
  let S := data i j r d
  Evaluates (checks xs s) i j r d ∧
  Interprets (checks xs s) S ∧ Rules S ∧
  CalibratedInputs s v ∧ UniqueResult v.applicationGuard ∧
  InputGuards i j r d v.applicationGuard ∧
  (∀ q, evaluate (chosenA v) (q ::ᵥ nil) = Encodable.encode (probe s q)) ∧
  (∀ t q, evaluate (chosenH v W) (t ::ᵥ q ::ᵥ nil) = (typed s t q).toNat) ∧
  (∀ c, TypedProbeTotal S v.applicationGuard (chosenH v W) (chosenA v) c) ∧
  OpenLiteralParsed v W ∧
  ∀ c, AlignedCarriersAt S v.applicationGuard (chosenH v W) (chosenA v) c

/-- Fresh interpretation and the existing original inference rules apply
to the new body of the exact numerically calibrated r′. -/
def ExactRefinedPresentationAndRules : Prop :=
  ∀ (xs : Entries) (s : Settings) (i j : Program 1) (r d : Program 3),
    Evaluates (checks xs s) i j r d →
    let R := refined i r
    let S := data i j R d
    Evaluates (checks xs s) i j R d ∧ Interprets (checks xs s) S ∧ Rules S

/-- At arbitrary already given actual programs, only r is changed.
The same W and same physical i/j/d/p/a/h and validity condition remain. -/
def ExactReinstallSameRefinedTuple : Prop :=
  ∀ (xs : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
    ∀ (i j : Program 1) (r d : Program 3) (v : Inputs),
      TupleAt xs s W i j r d v → TupleAt xs s W i j (refined i r) d v

/-- A single genuine concrete old choice supplies both packets and all
same selected leaves. The original actual ValidWindow stays explicit;
this does not assert the blocked fixed-source mixed integration. -/
def ExactReinstallConcreteRefinedTuple : Prop :=
  ∀ (xs : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
    ∃ (i j : Program 1) (r d : Program 3) (v : Inputs),
      TupleAt xs s W i j r d v ∧ TupleAt xs s W i j (refined i r) d v

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementReinstallTargets
