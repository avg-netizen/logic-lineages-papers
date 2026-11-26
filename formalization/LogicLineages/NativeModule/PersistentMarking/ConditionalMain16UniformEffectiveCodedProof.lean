module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalMain16UniformEffectiveCodedTargets
public import LogicLineages.NativeModule.PersistentMarking.ConditionalMain16UniformEffectiveProof
public import LogicLineages.NativeModule.PersistentMarking.NativeTowerCodeProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalMain16UniformEffectiveCodedProof
open ConditionalHeightEffectiveTargets ConditionalMain16UniformEffectiveCodedTargets

universe u

private theorem codedFamily {BH : Ordinal.{0}} (family : EffectiveCofinalFamily BH) :
    CodedEffectiveCofinalFamily BH := by
  refine ⟨NativeTowerCode.sequenceCodePrimitiveRecursive, ?_⟩
  intro S wfFull wfNative
  obtain ⟨t, literal, cofinal, below, notEqual⟩ := family S wfFull wfNative
  exact ⟨t, literal, (fun n => NativeTowerCode.nativeCodeCalibration S n (t n) (literal n)),
    cofinal, below, notEqual⟩

theorem exact_ConditionalMain16UniformEffectiveCoded : ConditionalMain16UniformEffectiveCoded.{u} := by
  intro I _ D BH norm uniform calibration tower identification
  have effective :=
    ConditionalMain16UniformEffectiveProof.exact_ConditionalMain16UniformEffective I D BH
      norm uniform calibration tower identification
  exact ⟨effective.1, effective.2.1, effective.2.2.1, codedFamily effective.2.2.2⟩

#print axioms exact_ConditionalMain16UniformEffectiveCoded

end LogicLineages.PersistentMarking.ConditionalMain16UniformEffectiveCodedProof
