module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeReinstallTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankApplicationReinstallTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenA)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalAtomicApplicationShapeReinstallTargets (BaseAt)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalNeutralRankGuard (rankApplication)
open NumberedWindowAddressApplication (graph)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowCopyAlgorithm (Entries)

/-- A distinct original-current input record, same other leaves literally.
The original proof using a different h is never moved to this selection. -/
def selectRankInputs (i g : Program 1) (v : Inputs) : Inputs where
  priorTyped := v.priorTyped
  optionApplication := v.optionApplication
  applicationGuard := rankApplication i g v.applicationGuard
  scalarProg := v.scalarProg
  freshBound := v.freshBound

/-- Exact all-input calibration of the actual newly chosen rank
application. No claim that a given g automatically supplies the fit. -/
def RankApplicationFit (s : Settings) (i g : Program 1) (p : Program 3) : Prop :=
  ∀ f u y, evaluate (rankApplication i g p) (f ::ᵥ u ::ᵥ y ::ᵥ nil) = (graph s f u y).toNat

def ExactNeutralRankApplicationReinstall : Prop :=
  ∀ (xs : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
    ∀ (i j g : Program 1) (r d : Program 3) (v : Inputs),
      RankApplicationFit s i g v.applicationGuard → BaseAt xs s i j r d v →
      let V := selectRankInputs i g v
      chosenA V = chosenA v ∧ TupleAt xs s W i j r d V

def ExactNeutralRankApplicationReselect : Prop :=
  ∀ (xs : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
    ∀ (i j g : Program 1) (r d : Program 3) (v : Inputs),
      RankApplicationFit s i g v.applicationGuard → TupleAt xs s W i j r d v →
      let V := selectRankInputs i g v
      chosenA V = chosenA v ∧ TupleAt xs s W i j r d V

end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankApplicationReinstallTargets
