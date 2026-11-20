module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementReinstallTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeReinstallTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowFormulaCalibrationTargets (Evaluates Interprets)
open NumberedWindowPresentationCheckers (checks)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalAccessibilityTargets (Rules)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowFunctionalGraphTargets (UniqueResult)
open NumberedWindowGuardedGraphTargets (InputGuards)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs CalibratedInputs)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalAtomicApplicationShape (refinedApplication)

/-- Actual one-field replacement with the same prior typed leaf, option
application, scalar, and fresh-bound programs. chosenA is unchanged by
definition; chosenH must be selected again from this exact record. -/
def refineInputs (v : Inputs) : Inputs where
  priorTyped := v.priorTyped
  optionApplication := v.optionApplication
  applicationGuard := refinedApplication v.applicationGuard
  scalarProg := v.scalarProg
  freshBound := v.freshBound

/-- Interface for the actual same source data and actual given old v.
The later assembly does not require any chosen old h, old totality, or
old alignment. In particular r is an arbitrary physical input leaf. -/
def BaseAt (xs : Entries) (s : Settings) (i j : Program 1) (r d : Program 3) (v : Inputs) : Prop :=
  let S := data i j r d
  Evaluates (checks xs s) i j r d ∧ Interprets (checks xs s) S ∧ Rules S ∧
  CalibratedInputs s v ∧ UniqueResult v.applicationGuard ∧ InputGuards i j r d v.applicationGuard

/-- Rebuild the complete original literal tuple on exactly the given
same body. Its p is the physical new shape checker and its h mentions
that checker. All original validity keeps the same explicit scope. -/
def ExactReinstallShapeRefinedApplication : Prop :=
  ∀ (xs : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
    ∀ (i j : Program 1) (r d : Program 3) (v : Inputs),
      BaseAt xs s i j r d v → TupleAt xs s W i j r d (refineInputs v)

/-- A caller with the existing whole selected tuple can use the same
physical inputs, without transporting derivations mentioning old h. -/
def ExactRefineExistingApplicationTuple : Prop :=
  ∀ (xs : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
    ∀ (i j : Program 1) (r d : Program 3) (v : Inputs),
      TupleAt xs s W i j r d v → TupleAt xs s W i j r d (refineInputs v)

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeReinstallTargets
