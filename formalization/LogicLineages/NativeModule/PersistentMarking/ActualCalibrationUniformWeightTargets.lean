module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationUniformTargets
public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationLevelsTargets

@[expose] public section

/-! # The calibration at every type level: weights (frozen before proof)

Local Fable-trio round, 27 November 2026, lane Fable A2. Plan and paper checks:
`verification/local-fable-trio-2026-11-27/fableA2/UNIFORM-INDUCTION-PLAN.md`.

A good object `F : A_{k+1}` has *weight* `σ` when, for every environment `xs` whose slots `j ≤ k`
hold objects of weights `ss j`, and under the chain condition `CondDown k ss σ`, the pair
`(Ω^(expDown k ss σ), appDown k F xs)` is a step. Applying weight `σ` to an argument of weight `ε`
gives weight `ε + Ω^σ` one type down (`expDown`); at type `A_1`, weight `σ` means "`(Ω^σ, H)` is a
step" (guarded by `Ω^σ < Λ`). `ExpSep ε σ` is the exponent-context condition of the level-2 targets
(`ExpCond`) with the norm `|σ|` in place of `σ` (weights are no longer countable) and without the
bound, which `CondDown` keeps once at the bottom of the chain.

Statements:
- `FamilyLifting`: the index hypotheses of `StepDiagonal` (`DiagFam`) and of `StepLimit` (`LimFam`)
  pass from a family of exponents `η a → T` to the family of indices `Ω^(expDown k ss (η a))`;
- `OrbitWeight`: the orbit of a weight-`σ` object from a weight-`σ'` object has weight
  `σ' + Ω^σ·a` at stage `a`;
- `TowerWeight`: every `B_m` has weight `0` (it adds `Ω^0 = 1` to the weight of its argument);
- `AllLevels`: root's per-level statements `LevelFactsAt l ∧ PsiTowerLevelAt l` for every `l ≥ 1`.

Nothing here asserts `AllTowerCalibration`; that is `exact_AllFromLevels` applied to `AllLevels`. -/

namespace LogicLineages.PersistentMarking.ActualCalibrationUniform
open Ordinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualCalibration ActualCalibrationThree
open ActualCalibrationStep ActualCalibrationLevels Paper16RemainingOrdinalTargets
open scoped Ordinal

/-- The exponent context `ε` admits adding `Ω^σ`: norm separation below `Ω^σ`, and adding `Ω^σ`
lowers neither the norm of `ε` nor that of `σ`. -/
def ExpSep (ε σ : Ordinal.{0}) : Prop :=
  NormSeparated ε σ ∧
  coefficientNorm ε ≤ coefficientNorm (ε + omegaIndex ^ σ) ∧
  coefficientNorm σ ≤ coefficientNorm (ε + omegaIndex ^ σ)

/-- The weight at type `A_1` after applying weight `σ` at type `A_{k+1}` down slots of weights
`ss k, …, ss 1`. -/
noncomputable def expDown : (k : Nat) → (Nat → Ordinal.{0}) → Ordinal.{0} → Ordinal.{0}
  | 0, _, σ => σ
  | k + 1, ss, σ => expDown k ss (ss (k + 1) + omegaIndex ^ σ)

/-- The chain of exponent-context conditions along `expDown`, with the bound at the bottom. -/
def CondDown : (k : Nat) → (Nat → Ordinal.{0}) → Ordinal.{0} → Prop
  | 0, _, σ => omegaIndex ^ σ < endpoint
  | k + 1, ss, σ => ExpSep (ss (k + 1)) σ ∧ CondDown k ss (ss (k + 1) + omegaIndex ^ σ)

/-- `F : A_{k+1}` has weight `σ` relative to the weighted environments in `E`. -/
def WeightAt (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (pow : CountableOrdinal → CountableOrdinal) (w : CountableOrdinal) (k : Nat)
    (E : Env → (Nat → Ordinal.{0}) → Prop) (σ : Ordinal.{0}) (F : Value (tier (k + 1))) : Prop :=
  GoodF fix pow w k F ∧
  ∀ (xs : Env) (ss : Nat → Ordinal.{0}), E xs ss → CondDown k ss σ →
    StepUp fix pow w (omegaIndex ^ expDown k ss σ) (appDown k F xs) ∧
    StepLow fix pow w (omegaIndex ^ expDown k ss σ) (appDown k F xs)

/-- The slots `1, …, k` hold objects of weights `ss 1, …, ss k`. -/
def WEnv (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (pow : CountableOrdinal → CountableOrdinal) (w : CountableOrdinal) :
    Nat → Env → (Nat → Ordinal.{0}) → Prop
  | 0 => fun _ _ => True
  | k + 1 => fun xs ss =>
      WEnv fix pow w k xs ss ∧ WeightAt fix pow w k (WEnv fix pow w k) (ss (k + 1)) (xs (k + 1))

/-- `F : A_{k+1}` has weight `σ`. -/
def WeightF (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (pow : CountableOrdinal → CountableOrdinal) (w : CountableOrdinal) (k : Nat) (σ : Ordinal.{0})
    (F : Value (tier (k + 1))) : Prop :=
  WeightAt fix pow w k (WEnv fix pow w k) σ F

/-- The index hypotheses of `StepDiagonal` for a family `η a → T`. -/
def DiagFam (η : CountableOrdinal → Ordinal.{0}) (T : Ordinal.{0}) : Prop :=
  (∀ a : CountableOrdinal, η a < T) ∧
  (∀ τ : Ordinal.{0}, τ < T → ∃ a b : CountableOrdinal,
    b.val = a.val + 1 ∧ a.val ≤ coefficientNorm τ ∧ τ < η b) ∧
  (∀ a : CountableOrdinal, 1 ≤ a.val → coefficientNorm (η a) ≤ max (coefficientNorm T) a.val) ∧
  (∀ (a : CountableOrdinal) (τ : Ordinal.{0}), 1 ≤ a.val → η a ≤ τ → τ < T →
    coefficientNorm (η a) ≤ coefficientNorm τ)

/-- The index hypotheses of `StepLimit` for a family `η β → T`, `β < l`. -/
def LimFam (l : CountableOrdinal) (η : CountableOrdinal → Ordinal.{0}) (T : Ordinal.{0}) : Prop :=
  (∀ β : CountableOrdinal, β.val < l.val → η β < T) ∧
  (∀ τ : Ordinal.{0}, τ < T → ∃ β : CountableOrdinal, β.val < l.val ∧ τ < η β) ∧
  (∀ β : CountableOrdinal, β.val < l.val → coefficientNorm (η β) ≤ coefficientNorm T) ∧
  (∀ (β : CountableOrdinal) (τ : Ordinal.{0}), β.val < l.val → η β ≤ τ → τ < T →
    coefficientNorm (η β) ≤ coefficientNorm τ)

/-- Family lifting along `expDown` and the final exponentiation. -/
def FamilyLifting : Prop :=
  (∀ (k : Nat) (ss : Nat → Ordinal.{0}) (η : CountableOrdinal → Ordinal.{0}) (T : Ordinal.{0}),
    DiagFam η T → CondDown k ss T →
    DiagFam (fun a => omegaIndex ^ expDown k ss (η a)) (omegaIndex ^ expDown k ss T)) ∧
  (∀ (k : Nat) (ss : Nat → Ordinal.{0}) (l : CountableOrdinal)
    (η : CountableOrdinal → Ordinal.{0}) (T : Ordinal.{0}), 0 < l.val →
    LimFam l η T → CondDown k ss T →
    LimFam l (fun β => omegaIndex ^ expDown k ss (η β)) (omegaIndex ^ expDown k ss T))

/-- The orbit of a weight-`σ` object from a weight-`σ'` object has weight `σ' + Ω^σ·a` at stage `a`. -/
def OrbitWeight : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    ∀ (k : Nat) (Ψ : Value (tier (k + 2))) (Φ : Value (tier (k + 1))) (σ σ' : Ordinal.{0}),
      WeightF fix pow w (k + 1) σ Ψ → WeightF fix pow w k σ' Φ →
      NormSeparated σ' (σ + 1) → omegaIndex ^ (σ + 1) ≤ endpoint →
      ∀ a : CountableOrdinal,
        WeightF fix pow w k (σ' + omegaIndex ^ σ * a.val) (orbit (tier (k + 1)) Ψ Φ a)

/-- Every `B_m` has weight `0`. -/
def TowerWeight : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    ∀ m : Nat, WeightF fix pow w (m + 1) 0 (towerValue fix m)

/-- Root's per-level statements at every level `l ≥ 1`. -/
def AllLevels : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    ∀ l : Nat, 1 ≤ l → LevelFactsAt fix pow w l ∧ PsiTowerLevelAt fix pow w l

end LogicLineages.PersistentMarking.ActualCalibrationUniform
