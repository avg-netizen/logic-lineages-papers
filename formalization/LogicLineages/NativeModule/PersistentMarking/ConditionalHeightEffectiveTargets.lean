module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalHeightTargets

@[expose] public section

/-! # `thm:height` with its effective cofinal witnesses (thm:main item 6)

Printed (thm:height, ordinals.tex 634–643, and thm:main item 6): the descending height of `⊐` is
BH, "already cofinally witnessed by closed native T terms of outer type o→o"; "Explicit native
terms realize ... a cofinal sequence of lower ranks"; "No individual term has been assigned rank BH".

Effectiveness: the native syntax `Spine.Expr` has no `Primcodable` instance. The witnesses are the
explicit family `NativeTowerSequenceTargets.sequenceTerm : ℕ → Expr` (#1462), a computable
(compiled, choice-free) Lean function defined by structural recursion on `n` and `l`; its recursion
equations are stated as theorems in the proof module. -/

namespace LogicLineages.PersistentMarking.ConditionalHeightEffectiveTargets
open Spine NativeIteratorStrictTargets NativeIndexedCarrierTargets NativeRankTargets
open NativeTowerSequenceTargets ConditionalTowerCofinality ExternalOrdinalInterfaceTargets
open ConditionalHeightTargets

universe u

/-- (a) the explicit family `n ↦ t_n`, (b) closed native of type σ = o→o, (c) ranks cofinal in BH,
(d) no rank equals BH (native ranks of the family, and every ordinary term's full rank). -/
def EffectiveCofinalFamily (BH : Ordinal.{0}) : Prop :=
  ∀ S (wfFull : WellFounded (fun t s : Expr => ConfinedPair.Strict S s t))
    (wfNative : WellFounded (@NativeBelow S indexType)),
    ∃ t : ℕ → ClosedNativeTerm S indexType,
      (∀ n, (t n).val = sequenceTerm n) ∧
      (∀ β, β < BH → ∃ n, β < nativeRank (wfNative.apply (t n))) ∧
      (∀ n, nativeRank (wfNative.apply (t n)) < BH) ∧
      (∀ q τ, PaperTerm S q τ → Ordinary q → confinedRank (wfFull.apply q) ≠ BH)

def HeightIsBHEffective (BH : Ordinal.{0}) : Prop :=
  HeightIsBH BH ∧ EffectiveCofinalFamily BH

def ConditionalHeightEffective : Prop :=
  ∀ (I : Type u) [LinearOrder I] (D : CollapseData I Ordinal.{0}) (BH : Ordinal.{0}),
    Calibration D → TowerHypotheses D → BHIdentification D BH → UpperBound BH →
    HeightIsBHEffective BH

end LogicLineages.PersistentMarking.ConditionalHeightEffectiveTargets
