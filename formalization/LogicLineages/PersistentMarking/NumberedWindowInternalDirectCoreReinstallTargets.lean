module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreNumericTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAccessibilityTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreReinstallTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowPresentationCheckers (checks)
open NumberedWindowFormulaCalibrationTargets (Evaluates Interprets)
open NumberedWindowInternalAccessibilityTargets (Rules)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalDirectBoundaryGuardsTargets (ScalarFit)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectCoreNumericTargets (PositiveFit CountFit)

def HeldThree (xs : Entries) (s : Settings) (i j : Program 1) (r : Program 3) : Prop :=
  ScalarFit i (checks xs s).scalar ∧
  (∀ x, evaluate j (x ::ᵥ nil) = ((checks xs s).multiset x).toNat) ∧
  PositiveFit r (checks xs s).positive

/-- The printed carrier/edge interpretations and object rule package
are freshly derived for this one body, with the selected dCore arrow. -/
def Reinstalled (xs : Entries) (s : Settings) (i j : Program 1) (r : Program 3) (count : Program 2) : Prop :=
  let d := dCore i r count
  let p := data i j r d
  Evaluates (checks xs s) i j r d ∧ Interprets (checks xs s) p ∧ Rules p

def ExactReinstall : Prop :=
  ∀ (xs : Entries) (s : Settings) (i j : Program 1) (r : Program 3) (count : Program 2),
    HeldThree xs s i j r → CountFit count → Reinstalled xs s i j r count

def ExactSelectedReinstall : Prop :=
  ∀ (xs : Entries) (s : Settings) (count : Program 2), CountFit count →
    ∃ (i j : Program 1) (r : Program 3), HeldThree xs s i j r ∧ Reinstalled xs s i j r count

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreReinstallTargets
