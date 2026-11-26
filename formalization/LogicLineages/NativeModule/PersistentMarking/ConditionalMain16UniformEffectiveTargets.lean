module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalMain16EffectiveTargets
public import LogicLineages.NativeModule.PersistentMarking.ConditionalUpperUniformTargets

@[expose] public section

/-! Paper 16's conditional principal theorem with both the uniform closed-theory
accessibility hypothesis and the explicit cofinal family of native terms.
The five named hypotheses are unchanged. This supporting target neither proves
those hypotheses nor promotes the numbered principal theorem. -/

namespace LogicLineages.PersistentMarking.ConditionalMain16UniformEffectiveTargets
open ExternalOrdinalInterfaceTargets ConditionalTowerCofinality

universe u

def ConditionalMain16UniformEffective : Prop :=
  ∀ (I : Type u) [LinearOrder I] (D : CollapseData I Ordinal.{0}) (BH : Ordinal.{0}),
    ExternalOrdinalInterfaceID1Targets.NormTheorem BH →
    ConditionalUpperUniformTargets.UniformAccessibility →
    Calibration D → TowerHypotheses D → BHIdentification D BH →
    ConditionalMain16EffectiveTargets.Main16StatementEffective BH

end LogicLineages.PersistentMarking.ConditionalMain16UniformEffectiveTargets
