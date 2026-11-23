module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalMain16Targets
public import LogicLineages.NativeModule.PersistentMarking.ConditionalUpperProof
public import LogicLineages.NativeModule.PersistentMarking.ConditionalHeightProof
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineDecisionSplitChecks
public import LogicLineages.NativeModule.PersistentMarking.StablePairChecks
public import LogicLineages.NativeModule.PersistentMarking.NativeOrientationChecks
public import LogicLineages.NativeModule.PersistentMarking.RankedRestrictionChecks

/-! Proof of the frozen `ConditionalMain16Targets.ConditionalMain16` (sha256 53387e55…998f):
items 1–5 from the accepted checks (on their module-system twins), item 6 from
`ConditionalUpperProof.exact_ConditionalUpper` (E4, R1) and Opus A's gated
`ConditionalHeightProof.conditionalHeight` (E1, E2, E3 and the upper bound). -/

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalMain16Proof
open ExternalOrdinalInterfaceTargets ConditionalTowerCofinality ConditionalMain16Targets

universe u

theorem exact_Items1to5 : Items1to5 :=
  ⟨ProtectedSpineDecisionSplitChecks.exact_Decidability, StablePairChecks.exact_fullStablePair,
    NumberedWindowExternalWellFoundedChecks.exact_ConfinedStrictWellFounded,
    NativeOrientationChecks.exact_fullOrientation, RankedRestrictionChecks.exact_ExactRankedRestriction⟩

theorem exact_ConditionalMain16 : ConditionalMain16.{u} := by
  intro I _ D BH norm individual calibration tower identification
  have upper := ConditionalUpperProof.exact_ConditionalUpper BH norm individual
  exact ⟨exact_Items1to5, upper.2,
    ConditionalHeightProof.conditionalHeight I D BH calibration tower identification upper.2⟩

#print axioms exact_Items1to5
#print axioms exact_ConditionalMain16

end LogicLineages.PersistentMarking.ConditionalMain16Proof
