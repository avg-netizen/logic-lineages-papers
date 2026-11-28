module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneTargetsV2
public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneOptionApplicationOpenV2
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedNumericChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneOptionReinstallV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.SourcePresentation ID1Completion.InternalControlGraph
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowInternalFreshProbeAlignmentChecks (exact_GivenFreshAlignmentAndCarriers)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs CalibratedInputs chosenA chosenH)
open NumberedWindowInternalFreshProbeParsedTypedNumericChecks (exact_ParsedTypedCalibration)
open NumberedWindowInternalFreshProbeParsedTypedObjectChecks
  (exact_SameParsedTypedProbeTotal exact_OpenLiteralParsedFresh)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalProbeTargets (OTerm TypedProbeTotal)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseApplicationFrontend (applicationCore applicationGuard)
open NumberedWindowInternalSparseTuple (InstalledTupleAt)
open NumberedWindowScalarAlgorithm (Settings)
open Paper16AccessibilityMilestoneOptionApplicationV2 (optionApplicationOf exact_OptionApplicationOfCalibration)
open Paper16AccessibilityMilestoneOptionApplicationOpenV2 (exact_OptionApplicationOfAccepted)
open Paper16AccessibilityMilestoneTargetsV2 (InstalledWindow)

def literalOptionInputs (i : Program 1) (least : Program 3) (v : Inputs) : Inputs :=
  { v with optionApplication := optionApplicationOf i least }

theorem exact_ReinstallLiteralOptionTuple {xs : Entries} {s : Settings} {W : List ProbeTy}
    {i j cv tv : Program 1} {d p₀ : Program 3} {raw : Program 5}
    {least : Program 3} {v : Inputs} (valid : ValidWindow s W)
    (installed : InstalledTupleAt xs s W i j cv tv d p₀ raw least v) :
    InstalledTupleAt xs s W i j cv tv d p₀ raw least (literalOptionInputs i least v) := by
  let updated := literalOptionInputs i least v
  let r := addressPositive cv tv raw least
  let presentation := data i j r d
  obtain ⟨tuple, app, callbacks, report⟩ := installed
  obtain ⟨values, meaning, rules, old, unique, guards, _, _, _, _, _⟩ := tuple
  have calibration : CalibratedInputs s updated :=
    ⟨old.1, old.2.1, exact_OptionApplicationOfCalibration s i least values.1 callbacks.2.2.2.1,
      old.2.2.2⟩
  obtain ⟨freshCal, typedCal⟩ := exact_ParsedTypedCalibration s W valid updated calibration
  have total (c : Nat) :
      TypedProbeTotal presentation updated.applicationGuard (chosenH updated W) (chosenA updated) c :=
    exact_SameParsedTypedProbeTotal updated W valid.2.1 presentation c
  exact ⟨⟨values, meaning, rules, calibration, unique, guards, freshCal, typedCal, total,
      exact_OpenLiteralParsedFresh updated W, fun c =>
        exact_GivenFreshAlignmentAndCarriers i j r d updated.applicationGuard
          (chosenH updated W) (chosenA updated) c guards (total c)⟩, app, callbacks, report⟩

/-- Rebuild the installed probe inputs with the literal binary option program. -/
def reinstallOptionApplication {S : Spine.Signature} {K : List Ty} {W : List ProbeTy}
    (A : InstalledWindow S K W) : InstalledWindow S K W :=
  { A with probes := literalOptionInputs A.scalar A.least A.probes
           installed := exact_ReinstallLiteralOptionTuple A.valid A.installed }

/-- At the installed application core, guard acceptance introduces the exact
chosen binary option report in the very same body. -/
theorem exact_ReinstalledOptionApplicationReport {S : Spine.Signature} {K : List Ty} {W : List ProbeTy}
    (A : InstalledWindow S K W) (c : Nat) (core : A.application = applicationCore A.least)
    {α : Type} {Γ : List (Formula α)} (q u v : OTerm α)
    (accepted : Nonempty (Derivation (sourceBody A.presentation c) Γ
      (programGraph A.probes.applicationGuard (suc z) ![q, u, v]))) :
    Nonempty (Derivation (sourceBody A.presentation c) Γ
      (programGraph (reinstallOptionApplication A).probes.optionApplication (suc v) ![q, u])) := by
  have guard : A.probes.applicationGuard = applicationGuard A.scalar A.least := by
    have paired := A.installed.2.1
    rw [core] at paired
    exact paired
  rw [guard] at accepted
  exact exact_OptionApplicationOfAccepted A.scalar A.least q u v accepted

#print axioms exact_ReinstallLiteralOptionTuple
#print axioms reinstallOptionApplication
#print axioms exact_ReinstalledOptionApplicationReport

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneOptionReinstallV2
