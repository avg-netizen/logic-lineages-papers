module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationThreePsiTargets

@[expose] public section

/-! # The step calculus at type `A_1` (frozen before proof)

The analytic core of the calibration at every tower level, abstracted from the n = 3 proof.
A *step* is a pair (`π` ordinal, `H : A_1`): in every admissible context `ζ` the collapse at
`ζ + π` is bounded above by `H x` when `ψ ζ ≤ x` (`StepUp`), and below by `H x` when `x ≤ ψ ζ`
and the index `ζ + π` is active (`StepLow`). Statements:

- `StepBase`: `(1, N_B)` is a step;
- `StepDiagonal`: the diagonal of a family of steps `(π_a, K_a)`, `a < Ω`, is a step
  `(π_Ω, x ↦ least fixed point of a ↦ K_a 0 above x)`, under explicit hypotheses on the family;
- `StepSuccessor`: if `(π, H)` is a step then `(π·Ω, B_0 H)` is a step.

Nothing here asserts that any particular higher-type object is a step; `NormPrincipal π` is a
hypothesis (it holds for `π = Ω^e`, `e` countable, by `norm_leading`). -/

namespace LogicLineages.PersistentMarking.ActualCalibrationStep
open Ordinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualCalibration ActualCalibrationThree
open scoped Ordinal

/-- An admissible context for the increment `π`: the index stays `≤ Λ`, and the norm of the
context separates from everything added below `π`. -/
def StepContext (ζ π : Ordinal.{0}) : Prop :=
  ζ + π ≤ endpoint ∧
  ∀ τ : Ordinal.{0}, τ < π → coefficientNorm (ζ + τ) = max (coefficientNorm ζ) (coefficientNorm τ)

/-- Upper half of a step. -/
def StepUp (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (pow : CountableOrdinal → CountableOrdinal) (w : CountableOrdinal) (π : Ordinal.{0})
    (H : CountableOrdinal → CountableOrdinal) : Prop :=
  ∀ (ζ : Ordinal.{0}) (x : CountableOrdinal), StepContext ζ π →
    Critical (veblenValue fix pow) (baseValue fix pow w) x.val →
    psiO fix pow w ζ ≤ x.val →
    psiO fix pow w (ζ + π) ≤ (H x).val

/-- Lower half of a step: needs the index `ζ + π` to be active. -/
def StepLow (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (pow : CountableOrdinal → CountableOrdinal) (w : CountableOrdinal) (π : Ordinal.{0})
    (H : CountableOrdinal → CountableOrdinal) : Prop :=
  ∀ (ζ : Ordinal.{0}) (x : CountableOrdinal), StepContext ζ π →
    coefficientNorm ζ < psiO fix pow w (ζ + π) →
    coefficientNorm π < psiO fix pow w (ζ + π) →
    x.val ≤ psiO fix pow w ζ →
    (H x).val ≤ psiO fix pow w (ζ + π)

/-- The norm of `π·c + τ` (`1 ≤ c < Ω`, `τ < π`) is `max (max c |π|) |τ|`. -/
def NormPrincipal (π : Ordinal.{0}) : Prop :=
  0 < π ∧ ∀ c τ : Ordinal.{0}, c ≠ 0 → c < omegaIndex → τ < π →
    coefficientNorm (π * c + τ) = max (max c (coefficientNorm π)) (coefficientNorm τ)

/-- `(1, N_B)` is a step. -/
def StepBase : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    StepUp fix pow w 1 (veblenValue fix pow) ∧ StepLow fix pow w 1 (veblenValue fix pow)

/-- The diagonal lemma. `π a`, `K a` (`a` countable) is the family, `πΩ` its supremum, and `D x`
the least fixed point of `a ↦ K a 0` above `x`. -/
def StepDiagonal : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    ∀ (π : CountableOrdinal → Ordinal.{0}) (πΩ : Ordinal.{0})
      (K : CountableOrdinal → CountableOrdinal → CountableOrdinal)
      (D : CountableOrdinal → CountableOrdinal),
      (∀ a : CountableOrdinal, 1 ≤ a.val → StepUp fix pow w (π a) (K a)) →
      (∀ a : CountableOrdinal, 1 ≤ a.val → StepLow fix pow w (π a) (K a)) →
      (∀ a : CountableOrdinal, π a < πΩ) →
      (∀ τ : Ordinal.{0}, τ < πΩ → ∃ a b : CountableOrdinal,
        b.val = a.val + 1 ∧ a.val ≤ coefficientNorm τ ∧ τ < π b) →
      (∀ a : CountableOrdinal, 1 ≤ a.val →
        coefficientNorm (π a) ≤ max (coefficientNorm πΩ) a.val) →
      (∀ (a : CountableOrdinal) (τ : Ordinal.{0}), 1 ≤ a.val → π a ≤ τ → τ < πΩ →
        coefficientNorm (π a) ≤ coefficientNorm τ) →
      (∀ a b x : CountableOrdinal, a.val ≤ b.val → (K a x).val ≤ (K b x).val) →
      (∀ a x y : CountableOrdinal, x.val ≤ y.val → (K a x).val ≤ (K a y).val) →
      (∀ a : CountableOrdinal, a.val ≤ (K a zeroValue).val) →
      (∀ l : CountableOrdinal, Order.IsSuccLimit l.val → ∀ b : Ordinal.{0},
        (∀ a : CountableOrdinal, a.val < l.val → (K a zeroValue).val ≤ b) →
        (K l zeroValue).val ≤ b) →
      (∀ κ : CountableOrdinal, K κ zeroValue = κ → 0 < κ.val →
        Order.IsSuccLimit κ.val ∧
        ∀ a x : CountableOrdinal, a.val < κ.val → x.val < κ.val → (K a x).val < κ.val) →
      (∀ κ : CountableOrdinal, K κ zeroValue = κ → (baseValue fix pow w).val < κ.val →
        Critical (veblenValue fix pow) (baseValue fix pow w) κ.val) →
      (∀ x : CountableOrdinal, K (D x) zeroValue = D x ∧ x.val < (D x).val ∧
        ∀ θ : CountableOrdinal, x.val < θ.val → K θ zeroValue = θ → (D x).val ≤ θ.val) →
      StepUp fix pow w πΩ D ∧ StepLow fix pow w πΩ D

/-- If `(π, H)` is a step (with `H` monotone inflationary, `≥ N_B`, critical-preserving, and `π`
norm-principal), then `(π·Ω, B_0 H)` is a step. -/
def StepSuccessor : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    ∀ (π : Ordinal.{0}) (H : CountableOrdinal → CountableOrdinal),
      NormPrincipal π →
      coefficientNorm π ≤ coefficientNorm (π * omegaIndex) →
      MonoInfl H →
      (∀ y : CountableOrdinal, (veblenValue fix pow y).val ≤ (H y).val) →
      (∀ x : CountableOrdinal, Critical (veblenValue fix pow) (baseValue fix pow w) x.val →
        Critical (veblenValue fix pow) (baseValue fix pow w) (H x).val) →
      StepUp fix pow w π H → StepLow fix pow w π H →
      StepUp fix pow w (π * omegaIndex) (towerValue fix 0 H) ∧
      StepLow fix pow w (π * omegaIndex) (towerValue fix 0 H)

end LogicLineages.PersistentMarking.ActualCalibrationStep
