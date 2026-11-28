module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationStepTargets

@[expose] public section

/-! # Steps along a `B_0`-orbit (frozen before proof)

`IsStep ε H`: `(Ω^ε, H)` is a step and `H` is a good function (monotone inflationary, `≥ N_B`,
critical-preserving). Statements:

- `StepLimit`: the limit rule — a step is the supremum of a norm-monotone family of steps;
- `StepB0Orbit`: "`B_0` has weight 1", iterated: if `(Ω^ε, H)` is a step and the norm of `ε`
  separates from countable summands, then `(Ω^(ε+e), B_0^e H)` is a step for every countable `e`.
  With `ε = 0`, `H = N_B` these are the n = 3 steps, now for every context `≤ Λ`.

Nothing is asserted about `B_1` or higher types. -/

namespace LogicLineages.PersistentMarking.ActualCalibrationStep
open Ordinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualCalibration ActualCalibrationThree
open scoped Ordinal

/-- Monotone inflationary, above `N_B`, and critical-preserving. -/
def GoodFn (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (pow : CountableOrdinal → CountableOrdinal) (w : CountableOrdinal)
    (H : CountableOrdinal → CountableOrdinal) : Prop :=
  MonoInfl H ∧ (∀ y : CountableOrdinal, (veblenValue fix pow y).val ≤ (H y).val) ∧
  ∀ x : CountableOrdinal, Critical (veblenValue fix pow) (baseValue fix pow w) x.val →
    Critical (veblenValue fix pow) (baseValue fix pow w) (H x).val

/-- `(Ω^ε, H)` is a step with a good function. -/
def IsStep (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (pow : CountableOrdinal → CountableOrdinal) (w : CountableOrdinal) (ε : Ordinal.{0})
    (H : CountableOrdinal → CountableOrdinal) : Prop :=
  GoodFn fix pow w H ∧ StepUp fix pow w (omegaIndex ^ ε) H ∧ StepLow fix pow w (omegaIndex ^ ε) H

/-- The limit rule. -/
def StepLimit : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    ∀ (l : CountableOrdinal) (π : CountableOrdinal → Ordinal.{0}) (πl : Ordinal.{0})
      (K : CountableOrdinal → CountableOrdinal → CountableOrdinal)
      (Hl : CountableOrdinal → CountableOrdinal),
      (∀ β : CountableOrdinal, β.val < l.val → StepUp fix pow w (π β) (K β)) →
      (∀ β : CountableOrdinal, β.val < l.val → StepLow fix pow w (π β) (K β)) →
      (∀ β : CountableOrdinal, β.val < l.val → π β < πl) →
      (∀ τ : Ordinal.{0}, τ < πl → ∃ β : CountableOrdinal, β.val < l.val ∧ τ < π β) →
      (∀ β : CountableOrdinal, β.val < l.val → coefficientNorm (π β) ≤ coefficientNorm πl) →
      (∀ (β : CountableOrdinal) (τ : Ordinal.{0}), β.val < l.val → π β ≤ τ → τ < πl →
        coefficientNorm (π β) ≤ coefficientNorm τ) →
      (∀ β x : CountableOrdinal, β.val < l.val → (K β x).val < (Hl x).val) →
      (∀ (x : CountableOrdinal) (b : Ordinal.{0}),
        (∀ β : CountableOrdinal, β.val < l.val → (K β x).val ≤ b) → (Hl x).val ≤ b) →
      (∀ x : CountableOrdinal, x.val < (Hl x).val) →
      (∀ x : CountableOrdinal, Critical (veblenValue fix pow) (baseValue fix pow w) x.val →
        Critical (veblenValue fix pow) (baseValue fix pow w) (Hl x).val) →
      StepUp fix pow w πl Hl ∧ StepLow fix pow w πl Hl

/-- Steps along the `B_0`-orbit of a step function. -/
def StepB0Orbit : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    ∀ (ε : Ordinal.{0}) (H : CountableOrdinal → CountableOrdinal),
      omegaIndex ^ (ε + omegaIndex) ≤ endpoint →
      NormSeparated ε 1 →
      IsStep fix pow w ε H →
      ∀ e : CountableOrdinal,
        IsStep fix pow w (ε + e.val) (orbit (tier 1) (towerValue fix 0) H e)

end LogicLineages.PersistentMarking.ActualCalibrationStep
