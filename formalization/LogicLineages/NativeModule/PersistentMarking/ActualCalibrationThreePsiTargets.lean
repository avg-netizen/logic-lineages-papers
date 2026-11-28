module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationThreeTargets

@[expose] public section

/-! # Calibration at n = 3, the ψ side: induction-loading statements (frozen before proof)

`T4` (`PsiPowerLevel`) is proved from two one-step inequalities about the (P)-collapse at an index
`ζ + Ω^e`, where `ζ` is an arbitrary context whose coefficient norm separates from what is added
below `Ω^e`. `D e = level fix pow e`, `E_β(α) = (D β)^α(0) = levelEnum fix pow β α`.
Nothing here describes ψ by a closed formula; no Cantor-normal-form recursion is claimed. -/

namespace LogicLineages.PersistentMarking.ActualCalibrationThree
open Ordinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualCalibration
open scoped Ordinal

/-- The level enumeration `E_β(α) = (D β)^α(0)`. -/
noncomputable def levelEnum (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (pow : CountableOrdinal → CountableOrdinal) (β α : CountableOrdinal) : CountableOrdinal :=
  orbit .base (level fix pow β) zeroValue α

/-- The actual collapse as a function on all ordinals (`0` above `Λ`, where it is not defined). -/
noncomputable def psiO (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (pow : CountableOrdinal → CountableOrdinal) (w : CountableOrdinal) (ξ : Ordinal.{0}) : Ordinal.{0} :=
  if h : ξ ≤ endpoint then (veblenData fix pow w).psi ⟨ξ, h⟩ else 0

/-- The coefficient norm of the context `ζ` separates from everything added below `Ω^e`. -/
def NormSeparated (ζ e : Ordinal.{0}) : Prop :=
  ∀ τ : Ordinal.{0}, τ < omegaIndex ^ e →
    coefficientNorm (ζ + τ) = max (coefficientNorm ζ) (coefficientNorm τ)

/-- Function side: `y + y ≤ N_B y`. -/
def VeblenDoubling : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    ∀ y : CountableOrdinal, y.val + y.val ≤ (veblenValue fix pow y).val

/-- Function side: strict T3 (`D β x < D (β+1) x`), and `L = (β ↦ D β 0)` is strictly increasing
and weakly inflationary. -/
def LevelStrict : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    (∀ β β' : CountableOrdinal, β'.val = β.val + 1 → ∀ x : CountableOrdinal,
      (level fix pow β x).val < (level fix pow β' x).val) ∧
    (∀ α β : CountableOrdinal, α.val < β.val →
      (level fix pow α zeroValue).val < (level fix pow β zeroValue).val) ∧
    ∀ α : CountableOrdinal, α.val ≤ (level fix pow α zeroValue).val

/-- Function side: every value of a level `D e`, `e ≥ 1`, is `N_B`-critical. -/
def LevelCritical : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    ∀ e : CountableOrdinal, 1 ≤ e.val → ∀ x : CountableOrdinal,
      Critical (veblenValue fix pow) (baseValue fix pow w) (level fix pow e x).val

/-- Function side: for `e ≥ 1`, `D e Γ_0 = D e 0`. -/
def LevelBaseRestart : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    ∀ e : CountableOrdinal, 1 ≤ e.val →
      level fix pow e (baseValue fix pow w) = level fix pow e zeroValue

/-- Upper step: if `ψ ζ ≤ x` with `x` critical, then `ψ(ζ + Ω^e) ≤ D e x`. -/
def UpperStep : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    ∀ (e : CountableOrdinal) (ζ : Ordinal.{0}) (x : CountableOrdinal),
      ζ + omegaIndex ^ e.val ≤ omegaIndex ^ omegaIndex →
      NormSeparated ζ e.val →
      Critical (veblenValue fix pow) (baseValue fix pow w) x.val →
      psiO fix pow w ζ ≤ x.val →
      psiO fix pow w (ζ + omegaIndex ^ e.val) ≤ (level fix pow e x).val

/-- Lower step: if `x ≤ ψ ζ` and the index `ζ + Ω^e` is active (`|ζ|` and `e` lie below its
ψ-value), then `D e x ≤ ψ(ζ + Ω^e)`. -/
def LowerStep : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    ∀ (e : CountableOrdinal) (ζ : Ordinal.{0}) (x : CountableOrdinal),
      ζ + omegaIndex ^ e.val ≤ omegaIndex ^ omegaIndex →
      NormSeparated ζ e.val →
      coefficientNorm ζ < psiO fix pow w (ζ + omegaIndex ^ e.val) →
      e.val < psiO fix pow w (ζ + omegaIndex ^ e.val) →
      x.val ≤ psiO fix pow w ζ →
      (level fix pow e x).val ≤ psiO fix pow w (ζ + omegaIndex ^ e.val)

end LogicLineages.PersistentMarking.ActualCalibrationThree
