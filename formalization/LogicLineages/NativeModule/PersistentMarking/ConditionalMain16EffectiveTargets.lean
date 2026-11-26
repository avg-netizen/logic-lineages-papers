module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalMain16Targets
public import LogicLineages.NativeModule.PersistentMarking.ConditionalHeightEffectiveTargets

@[expose] public section

/-! Paper 16 `thm:main` with item 6 in its printed effective form: the explicit family of closed
native terms of type o→o has cofinal ranks (`HeightIsBHEffective`). Same hypotheses as
`ConditionalMain16Targets.ConditionalMain16`. -/

namespace LogicLineages.PersistentMarking.ConditionalMain16EffectiveTargets
open ExternalOrdinalInterfaceTargets ConditionalTowerCofinality ConditionalMain16Targets
open ConditionalHeightEffectiveTargets

universe u

def Main16StatementEffective (BH : Ordinal.{0}) : Prop :=
  Items1to5 ∧ UpperBound BH ∧ HeightIsBHEffective BH

def ConditionalMain16Effective : Prop :=
  ∀ (I : Type u) [LinearOrder I] (D : CollapseData I Ordinal.{0}) (BH : Ordinal.{0}),
    ExternalOrdinalInterfaceID1Targets.NormTheorem BH → ConditionalUpperTargets.IndividualAccessibility →
    Calibration D → TowerHypotheses D → BHIdentification D BH →
    Main16StatementEffective BH

end LogicLineages.PersistentMarking.ConditionalMain16EffectiveTargets
