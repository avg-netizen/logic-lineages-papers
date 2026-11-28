module

public import LogicLineages.NativeModule.PersistentMarking.ActualCollapseDefinitions

@[expose] public section

/-! # The index families of the calibration, at every tower level

Frozen before proof (local Fable-trio round, 27 November 2026, root lane).

`towerIndex k e` is the tower of `k` exponentiations of `Ω` with the countable `e` on top:
`e`, `Ω^e`, `Ω^(Ω^e)`, … . Below the tower argument `a_{k+2}` (`a_2 = Ω`, `a_3 = Ω^Ω`, …) these are the
indices along which the collapse is compared with the level functions. The statement gives, for
every `k`, the three facts the diagonal step (`CollapseDiagonal.DiagonalHypotheses`: `below`,
`norm`, `cover`) uses about them. For `k = 1` it is `PowerIndexFacts` of the n = 3 reduction. -/

namespace LogicLineages.PersistentMarking.ActualTowerIndex
open Ordinal ActualOmegaTower ActualCollapse
open scoped Ordinal

/-- `e`, `Ω^e`, `Ω^(Ω^e)`, … -/
noncomputable def towerIndex : Nat → Ordinal.{0} → Ordinal.{0}
  | 0, e => e
  | k + 1, e => omegaIndex ^ towerIndex k e

/-- For every level `k` and countable `e`: the index lies below `a_{k+2}`; its norm is at most `e`
(for `e ≥ 1`); and every index below `a_{k+2}` whose norm is below `e` lies below it. -/
def TowerIndexFacts : Prop :=
  ∀ k : Nat,
    (∀ e : Ordinal.{0}, e < omegaIndex → towerIndex k e < argument (k + 2)) ∧
    (∀ e : Ordinal.{0}, 1 ≤ e → e < omegaIndex → coefficientNorm (towerIndex k e) ≤ e) ∧
    (∀ η e : Ordinal.{0}, η < argument (k + 2) → 1 ≤ e → e < omegaIndex →
      coefficientNorm η < e → η < towerIndex k e)

end LogicLineages.PersistentMarking.ActualTowerIndex
