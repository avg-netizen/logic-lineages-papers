module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneTargetsV2
public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestonePriorTypedCalibrationV2
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedNumericChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneLiteralPriorTypedV2

open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowFunctionalGraphTargets (UniqueResult)
open NumberedWindowGuardedGraphTargets (InputGuards)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowInternalFreshProbeAlignmentChecks (exact_GivenFreshAlignmentAndCarriers)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped
  (Inputs CalibratedInputs chosenA chosenH)
open NumberedWindowInternalFreshProbeParsedTypedNumericChecks
  (exact_ParsedTypedCalibration)
open NumberedWindowInternalFreshProbeParsedTypedObjectChecks
  (exact_SameParsedTypedProbeTotal exact_OpenLiteralParsedFresh)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalProbeTargets (TypedProbeTotal)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseTuple (InstalledTupleAt)
open NumberedWindowScalarAlgorithm (Settings)
open Paper16AccessibilityMilestoneTargetsV2 (InstalledWindow)

/-- Use the new prior checker in the same probe inputs. -/
def literalPriorTypedInputs (i : Program 1) (v : Inputs) : Inputs :=
  { v with priorTyped := priorTypedOf i }

private theorem reinstallCalibratedInputs {xs : Entries} {s : Settings} {W : List ProbeTy}
    {i j cv tv : Program 1} {d p₀ : Program 3} {raw : Program 5}
    {least : Program 3} {v updated : Inputs} (valid : ValidWindow s W)
    (installed : InstalledTupleAt xs s W i j cv tv d p₀ raw least v)
    (sameGuard : updated.applicationGuard = v.applicationGuard)
    (newCalibration : CalibratedInputs s updated) :
    InstalledTupleAt xs s W i j cv tv d p₀ raw least updated := by
  let r := addressPositive cv tv raw least
  let presentation := data i j r d
  obtain ⟨tuple, app, callbacks, report⟩ := installed
  obtain ⟨values, meaning, rules, _, unique, guards, _, _, _, _, _⟩ := tuple
  have unique' : UniqueResult updated.applicationGuard := by
    rw [sameGuard]
    exact unique
  have guards' : InputGuards i j r d updated.applicationGuard := by
    rw [sameGuard]
    exact guards
  obtain ⟨freshCal, typedCal⟩ := exact_ParsedTypedCalibration s W valid updated newCalibration
  have total (c : Nat) :
      TypedProbeTotal presentation updated.applicationGuard (chosenH updated W) (chosenA updated) c :=
    exact_SameParsedTypedProbeTotal updated W valid.2.1 presentation c
  exact ⟨⟨values, meaning, rules, newCalibration, unique', guards', freshCal, typedCal, total,
      exact_OpenLiteralParsedFresh updated W, fun c =>
        exact_GivenFreshAlignmentAndCarriers i j r d updated.applicationGuard
          (chosenH updated W) (chosenA updated) c guards' (total c)⟩,
    sameGuard.trans app, callbacks, report⟩

theorem exact_ReinstallLiteralPriorTypedTuple {xs : Entries} {s : Settings} {W : List ProbeTy}
    {i j cv tv : Program 1} {d p₀ : Program 3} {raw : Program 5}
    {least : Program 3} {v : Inputs} (valid : ValidWindow s W)
    (installed : InstalledTupleAt xs s W i j cv tv d p₀ raw least v) :
    InstalledTupleAt xs s W i j cv tv d p₀ raw least (literalPriorTypedInputs i v) := by
  have old := installed.1.2.2.2.1
  exact reinstallCalibratedInputs valid installed rfl
    ⟨old.1, exact_PriorTypedOfCalibration s i installed.1.1.1, old.2.2⟩

/-- Reinstall the prior type checker at the same original presentation,
with the same path, least representative, application and fresh programs. -/
def retypeWindow {S : Spine.Signature} {K : List Ty} {W : List ProbeTy}
    (A : InstalledWindow S K W) : InstalledWindow S K W :=
  { A with probes := literalPriorTypedInputs A.scalar A.probes
           installed := exact_ReinstallLiteralPriorTypedTuple A.valid A.installed }

/-- The fresh selector uses the installed scalar on its original source address. -/
def literalFreshScalarInputs (i : Program 1) (v : Inputs) : Inputs :=
  { v with scalarProg := i }

theorem exact_ReinstallLiteralFreshScalarTuple {xs : Entries} {s : Settings} {W : List ProbeTy}
    {i j cv tv : Program 1} {d p₀ : Program 3} {raw : Program 5}
    {least : Program 3} {v : Inputs} (valid : ValidWindow s W)
    (installed : InstalledTupleAt xs s W i j cv tv d p₀ raw least v) :
    InstalledTupleAt xs s W i j cv tv d p₀ raw least (literalFreshScalarInputs i v) := by
  have old := installed.1.2.2.2.1
  exact reinstallCalibratedInputs valid installed rfl
    ⟨⟨installed.1.1.1, old.1.2⟩, old.2⟩

/-- Use the installed scalar in the fresh selector and rebuild the parsed probes. -/
def reinstallFreshScalar {S : Spine.Signature} {K : List Ty} {W : List ProbeTy}
    (A : InstalledWindow S K W) : InstalledWindow S K W :=
  { A with probes := literalFreshScalarInputs A.scalar A.probes
           installed := exact_ReinstallLiteralFreshScalarTuple A.valid A.installed }

#print axioms exact_ReinstallLiteralPriorTypedTuple
#print axioms retypeWindow
#print axioms exact_ReinstallLiteralFreshScalarTuple
#print axioms reinstallFreshScalar

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneLiteralPriorTypedV2
