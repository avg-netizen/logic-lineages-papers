module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomMembershipDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeReinstallTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomMembershipTupleTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowFormulaCalibrationTargets (Evaluates Interprets)
open NumberedWindowPresentationCheckers (checks)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalAccessibilityTargets (Rules)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalAtomicApplicationShapeReinstallTargets (refineInputs)
open NumberedWindowInternalAuxBottomMembership (augmented)

/-- Original all-raw evaluation and fresh interpretation/Rules for
this actual data, with only the positive checker r replaced. -/
def ExactAugmentedPresentation : Prop :=
  ∀ (xs : Entries) (s : Settings) (i j : Program 1) (r d : Program 3),
    Evaluates (checks xs s) i j r d →
    let R := augmented i r
    let S := data i j R d
    Evaluates (checks xs s) i j R d ∧ Interprets (checks xs s) S ∧ Rules S

/-- New same-physical v fields, same source i/j/d, rebuilt same-body
presentation, the actual p-star and its freshly assembled h-star. -/
def ExactReinstallAugmentedShapeTuple : Prop :=
  ∀ (xs : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
    ∀ (i j : Program 1) (r d : Program 3) (v : Inputs),
    TupleAt xs s W i j r d v →
      TupleAt xs s W i j (augmented i r) d (refineInputs v)

/-- One actual original choice of programs, used on both sides.
No fixed-source mixed bridge or arbitrary output carrier is assumed. -/
def ExactConcreteAugmentedShapeTuple : Prop :=
  ∀ (xs : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
    ∃ (i j : Program 1) (r d : Program 3) (v : Inputs),
      TupleAt xs s W i j r d v ∧
      TupleAt xs s W i j (augmented i r) d (refineInputs v)

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomMembershipTupleTargets
