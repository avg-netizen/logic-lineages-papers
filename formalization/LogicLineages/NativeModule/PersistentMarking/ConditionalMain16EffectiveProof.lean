module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalMain16EffectiveTargets
public import LogicLineages.NativeModule.PersistentMarking.ConditionalMain16Proof
public import LogicLineages.NativeModule.PersistentMarking.ConditionalHeightEffectiveProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalMain16EffectiveProof
open ConditionalMain16EffectiveTargets

universe u

theorem exact_ConditionalMain16Effective : ConditionalMain16Effective.{u} := by
  intro I _ D BH norm individual calibration tower identification
  have main := ConditionalMain16Proof.exact_ConditionalMain16 I D BH norm individual calibration tower identification
  exact ⟨main.1, main.2.1, ConditionalHeightEffectiveProof.conditionalHeightEffective I D BH
    calibration tower identification main.2.1⟩

#print axioms exact_ConditionalMain16Effective

end LogicLineages.PersistentMarking.ConditionalMain16EffectiveProof
