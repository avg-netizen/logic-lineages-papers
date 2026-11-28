module

public import LogicLineages.NativeModule.PersistentMarking.Paper16RemainingOrdinalTargets
public import LogicLineages.NativeModule.PersistentMarking.ActualTowerIndexTargets

@[expose] public section

/-! # The calibration at every tower level, reduced to per-level statements

Frozen before proof (local Fable-trio round, 27 November 2026, root lane).

`Δ_{l+2}' = B_l B_{l-1} ⋯ B_0 N_B Γ_0`. With the environment `towerEnv` holding `N_B` in slot 1 and
`B_j` in slot `j+2`, the composite is `fix` of the level diagonal
`levelDiagonal l α = (B_{l-1}^α B_{l-2}) ⋯ N_B 0` (`l = 1`: `B_0^α(N_B)(0)`), applied to `Γ_0`
(`DiagonalUnfolding`). `CalibrationStep` then gives `Δ_{l+2}' = ψ(a_{l+2})` from two kinds of
per-level input, neither asserted here:

- `LevelFactsAt l`: the diagonal is strictly increasing, exceeds `Γ_0` from 1 on, and is the
  supremum of its earlier values at limits;
- `PsiTowerLevelAt l`: `ψ(towerIndex l e) = levelDiagonal l e` while the diagonal has no fixed
  point in `[1, e]` (for `l = 1` this is T4, `ActualCalibrationThree.PsiPowerLevel`).

For `l ≥ 2` nobody has checked that these per-level inputs are the right (true) statements; the
implication is what is claimed. `l = 0` is excluded in `AllFromLevels`: there the collapse along
countable indices is the orbit from `Γ_0`, not from 0, and `n = 2` is a theorem by another route. -/

namespace LogicLineages.PersistentMarking.ActualCalibrationLevels
open Ordinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualTowerIndex
open Paper16RemainingOrdinalTargets
open scoped Ordinal

/-- Slot 1 holds `N_B`, slot `j+2` holds `B_j`. -/
noncomputable def towerEnv (fix : Value (tier 2)) (pow : Value (tier 1)) : Env
  | 0 => zeroValue
  | 1 => veblenValue fix pow
  | j + 2 => towerValue fix j

/-- The level diagonal `α ↦ (B_{l-1}^α B_{l-2}) ⋯ N_B 0`. -/
noncomputable def levelDiagonal (fix : Value (tier 2)) (pow : Value (tier 1)) (l : Nat) :
    CountableOrdinal → CountableOrdinal :=
  fun α => spineValue l (towerEnv fix pow) α

/-- `Δ_{l+2}'` is `fix` of the level diagonal at `Γ_0`. -/
def DiagonalUnfolding : Prop :=
  ∀ (fix : Value (tier 2)) (pow : Value (tier 1)) (w : CountableOrdinal) (l : Nat),
    sequenceValue fix pow w (l + 2) = fix (levelDiagonal fix pow l) (baseValue fix pow w)

/-- The function-side input at level `l`. -/
def LevelFactsAt (fix : Value (tier 2)) (pow : Value (tier 1)) (w : CountableOrdinal) (l : Nat) : Prop :=
  (∀ α β : CountableOrdinal, α.val < β.val →
    (levelDiagonal fix pow l α).val < (levelDiagonal fix pow l β).val) ∧
  (∀ e : CountableOrdinal, 1 ≤ e.val → (baseValue fix pow w).val < (levelDiagonal fix pow l e).val) ∧
  (∀ lim : CountableOrdinal, Order.IsSuccLimit lim.val →
    (levelDiagonal fix pow l lim).val =
      ⨆ e : EarlierStages lim, (levelDiagonal fix pow l (earlierStage lim e)).val)

/-- The collapse-side input at level `l`: the collapse along the tower indices. -/
def PsiTowerLevelAt (fix : Value (tier 2)) (pow : Value (tier 1)) (w : CountableOrdinal) (l : Nat) : Prop :=
  ∀ e : CountableOrdinal, 1 ≤ e.val →
    (∀ θ : CountableOrdinal, 1 ≤ θ.val → θ.val ≤ e.val → levelDiagonal fix pow l θ ≠ θ) →
    ∀ h : towerIndex l e.val ≤ endpoint,
      (veblenData fix pow w).psi ⟨towerIndex l e.val, h⟩ = (levelDiagonal fix pow l e).val

/-- One level of the calibration from its two inputs. -/
def CalibrationStep : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    ∀ l : Nat, LevelFactsAt fix pow w l → PsiTowerLevelAt fix pow w l →
      (sequenceValue fix pow w (l + 2)).val = (veblenData fix pow w).psi (actualArgument (l + 2))

/-- The whole calibration from the per-level inputs at every level `l ≥ 1`. -/
def AllFromLevels : Prop :=
  (∀ (A : OrdinalSemantics) (l : Nat), 1 ≤ l →
      LevelFactsAt A.fix A.pow A.omega l ∧ PsiTowerLevelAt A.fix A.pow A.omega l) →
    AllTowerCalibration

end LogicLineages.PersistentMarking.ActualCalibrationLevels
