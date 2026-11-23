module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalUpperUniformProof
public import LogicLineages.NativeModule.PersistentMarking.ConditionalMain16Proof

/-! Conditional Paper 16 `thm:main` with the uniform internal hypothesis, from #1467
(`exact_ConditionalMain16`) and the bridge. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalUpperUniformMain16Proof
open ConditionalUpperUniformTargets

universe u

theorem exact_ConditionalMain16Uniform : ConditionalMain16Uniform.{u} := by
  intro I _ D BH norm uniform calibration tower identification
  exact ConditionalMain16Proof.exact_ConditionalMain16 I D BH norm
    (ConditionalUpperUniformProof.individualOfUniform uniform) calibration tower identification

#print axioms exact_ConditionalMain16Uniform

end LogicLineages.PersistentMarking.ConditionalUpperUniformMain16Proof
