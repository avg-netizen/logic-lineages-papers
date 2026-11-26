module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalMain16UniformEffectiveTargets
public import LogicLineages.NativeModule.PersistentMarking.ConditionalMain16EffectiveProof
public import LogicLineages.NativeModule.PersistentMarking.ConditionalUpperUniformProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalMain16UniformEffectiveProof
open ConditionalMain16UniformEffectiveTargets

universe u

theorem exact_ConditionalMain16UniformEffective : ConditionalMain16UniformEffective.{u} := by
  intro I _ D BH norm uniform calibration tower identification
  exact ConditionalMain16EffectiveProof.exact_ConditionalMain16Effective I D BH norm
    (ConditionalUpperUniformProof.individualOfUniform uniform) calibration tower identification

#print axioms exact_ConditionalMain16UniformEffective

end LogicLineages.PersistentMarking.ConditionalMain16UniformEffectiveProof
