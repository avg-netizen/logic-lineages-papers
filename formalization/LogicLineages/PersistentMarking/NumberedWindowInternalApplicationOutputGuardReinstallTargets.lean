module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeReinstallTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalApplicationOutputGuardTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalApplicationOutputGuardReinstallTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenA)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalAtomicApplicationShapeReinstallTargets (BaseAt)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalAtomicApplicationShape (refinedApplication)
open NumberedWindowInternalApplicationOutputGuardTargets (outputGuard)
open NumberedWindowAddressApplication (graph)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowCopyAlgorithm (Entries)

/-- A distinct original-current input record, same other leaves literally.
The original proof using a different h is never moved to this selection. -/
def selectOutputInputs (i : Program 1) (v : Inputs) : Inputs where
  priorTyped := v.priorTyped
  optionApplication := v.optionApplication
  applicationGuard := outputGuard i (refinedApplication v.applicationGuard)
  scalarProg := v.scalarProg
  freshBound := v.freshBound

/-- Numerical closure only; neither a formula nor an object inference.
This is not assumed to hold for arbitrary settings without a supplier. -/
def OutputScalarLaw (s : Settings) (i : Program 1) : Prop :=
  ∀ f u y, graph s f u y = true → evaluate i (y ::ᵥ nil) = 1

def ExactApplicationOutputGuardReinstall : Prop :=
  ∀ (xs : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
    ∀ (i j : Program 1) (r d : Program 3) (v : Inputs),
      OutputScalarLaw s i → BaseAt xs s i j r d v →
      let V := selectOutputInputs i v
      chosenA V = chosenA v ∧ TupleAt xs s W i j r d V

def ExactApplicationOutputGuardReselect : Prop :=
  ∀ (xs : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
    ∀ (i j : Program 1) (r d : Program 3) (v : Inputs),
      OutputScalarLaw s i → TupleAt xs s W i j r d v →
      let V := selectOutputInputs i v
      chosenA V = chosenA v ∧ TupleAt xs s W i j r d V

end LogicLineages.PersistentMarking.NumberedWindowInternalApplicationOutputGuardReinstallTargets
