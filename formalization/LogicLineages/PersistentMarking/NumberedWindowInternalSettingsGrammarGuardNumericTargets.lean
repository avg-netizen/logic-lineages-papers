module

public import LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowStepTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardNumericTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalAuxWindowStepTargets (TypeGuardCalibrated)
open NumberedWindowInternalSettingsGrammarGuardDefinitions

/-- A same-Settings list inclusion; no guard calibration or open graph
theorem is included in this premise. -/
def GrammarTypeInclusion (s : Settings) : Prop := ∀ n, n ∈ s.window.1 → n ∈ s.types

/-- Preserve the real original type guard, on every natural input, provided
the actual window types are among the actual grammar types. -/
def ExactSettingsRefitGuardCalibration : Prop :=
  ∀ (s : Settings) (T : Program 1), GrammarTypeInclusion s →
    TypeGuardCalibrated s T → TypeGuardCalibrated s (refitGuard s T)

end LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardNumericTargets
