module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalUpperTargets
public import LogicLineages.NativeModule.PersistentMarking.ConditionalHeightTargets
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineDecisionTargets
public import LogicLineages.NativeModule.PersistentMarking.StablePairTargets
public import LogicLineages.NativeModule.PersistentMarking.NativeOrientationTargets
public import LogicLineages.NativeModule.PersistentMarking.RankedRestrictionTargets

/-! Conditional Paper 16 `thm:main` (paper.tex 96–116; Opus B, round 4; not a twin).

Items 1–5 are the accepted targets of the numbered statements they restate (register
`formal_target`s, read against the printed clauses in `round4/opusB/MAIN16-SOURCE-MAP.md`):
1 `thm:decide` (#416) `ProtectedSpineDecisionTargets.Decidability`;
2 `thm:stable` (#178) `StablePairTargets.FullStablePair` (order laws) and #489
  `ConfinedStrictWellFounded` (strict part well founded);
3 the stability clauses of the same `FullStablePair`;
4 `thm:orient` (#193) `NativeOrientationTargets.FullOrientation`;
5 `thm:rpo` (#406) `RankedRestrictionTargets.ExactRankedRestriction`.
Item 6 is `UpperBound BH` (shared interface def; `thm:upper`) ∧ `HeightIsBH BH` (Opus A's
`thm:height`), with `BH` abstract. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalMain16Targets
open ExternalOrdinalInterfaceTargets ConditionalTowerCofinality

universe u

def Items1to5 : Prop :=
  ProtectedSpineDecisionTargets.Decidability ∧
  StablePairTargets.FullStablePair ∧
  NumberedWindowExternalWellFoundedTargets.ConfinedStrictWellFounded ∧
  NativeOrientationTargets.FullOrientation ∧
  RankedRestrictionTargets.ExactRankedRestriction

def Main16Statement (BH : Ordinal.{0}) : Prop :=
  Items1to5 ∧ UpperBound BH ∧ ConditionalHeightTargets.HeightIsBH BH

/-- Conditional `thm:main`: every external input of `thm:upper` (E4, R1) and of `thm:height`
(E1, E2, E3) as a named hypothesis over abstract collapse data and an abstract `BH`. -/
def ConditionalMain16 : Prop :=
  ∀ (I : Type u) [LinearOrder I] (D : CollapseData I Ordinal.{0}) (BH : Ordinal.{0}),
    ExternalOrdinalInterfaceID1Targets.NormTheorem BH → ConditionalUpperTargets.IndividualAccessibility →
    Calibration D → TowerHypotheses D → BHIdentification D BH →
    Main16Statement BH

end LogicLineages.PersistentMarking.ConditionalMain16Targets
