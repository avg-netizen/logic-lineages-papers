module

public import LogicLineages.NativeModule.PersistentMarking.ExternalOrdinalInterfaceTargets

@[expose] public section

/-! # Paper 16 `thm:height` (ordinals.tex 634–643), conditional on the external interface

Printed: "The descending height of ⊐ is BH, already cofinally witnessed by closed native T terms
of outer type o→o." Heights are suprema of rank + 1 (#1448 rank vocabulary): over the ordinary
terms for the full confined strict relation, and over the closed native terms of type σ = o→o for
their restriction. -/

namespace LogicLineages.PersistentMarking.ConditionalHeightTargets
open Spine NativeIteratorStrictTargets NativeIndexedCarrierTargets NativeRankTargets
open ConditionalTowerCofinality ExternalOrdinalInterfaceTargets

universe u

/-- The ordinary terms of a signature (the field of `⊐` that `thm:upper` bounds). -/
def OrdinaryTerm (S : Signature) : Type := {q : Expr // ∃ τ, PaperTerm S q τ ∧ Ordinary q}

/-- The descending height of `⊐`: the supremum of rank + 1 over ordinary terms. -/
noncomputable def descendingHeight (S : Signature)
    (wf : WellFounded (fun t s : Expr => ConfinedPair.Strict S s t)) : Ordinal.{0} :=
  ⨆ q : OrdinaryTerm S, Order.succ (confinedRank (wf.apply q.val))

/-- The height of the restriction to closed native terms of outer type σ = o→o. -/
noncomputable def nativeHeight (S : Signature) (wf : WellFounded (@NativeBelow S indexType)) :
    Ordinal.{0} :=
  ⨆ t : ClosedNativeTerm S indexType, Order.succ (nativeRank (wf.apply t))

/-- The printed conclusion, for every signature. -/
def HeightIsBH (BH : Ordinal.{0}) : Prop :=
  ∀ S (wfFull : WellFounded (fun t s : Expr => ConfinedPair.Strict S s t))
    (wfNative : WellFounded (@NativeBelow S indexType)),
    descendingHeight S wfFull = BH ∧ nativeHeight S wfNative = BH

/-- `thm:height` from the cited inputs: E1 calibration, E2 (P) and the printed tower facts,
E3 the endpoint identification, and the conclusion of `thm:upper`. -/
def ConditionalHeight : Prop :=
  ∀ (I : Type u) [LinearOrder I] (D : CollapseData I Ordinal.{0}) (BH : Ordinal.{0}),
    Calibration D → TowerHypotheses D → BHIdentification D BH → UpperBound BH → HeightIsBH BH

end LogicLineages.PersistentMarking.ConditionalHeightTargets
