module

public import LogicLineages.NativeModule.PersistentMarking.ActualCollapseMainTargets

@[expose] public section

/-! # Calibration on the actual data: monotonicity, orbit comparison, and the instance n = 2

All statements concern the repository's semantic `N_B = veblenValue fix pow` (#1462), its building
blocks `Next = fix pow`, `B_0 = towerValue fix 0`, and the (P)-defined collapse (#1486). -/

namespace LogicLineages.PersistentMarking.ActualCalibration
open Ordinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets NativeTowerTargets NativeTowerSequenceTargets
open ActualCollapse
open scoped Ordinal

/-- Monotone (in the ordinal value) and strictly inflationary. -/
def MonoInfl (f : CountableOrdinal → CountableOrdinal) : Prop :=
  (∀ x y : CountableOrdinal, x.val ≤ y.val → (f x).val ≤ (f y).val) ∧ Inflationary f

/-- Layer 1: `Next`, every `B_0`-image of a monotone inflationary function, and `N_B` are
monotone and inflationary. -/
def MonotoneLayer : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    MonoInfl (fix pow) ∧
    (∀ h, MonoInfl h → MonoInfl (towerValue fix 0 h) ∧ ∀ x, (h x).val ≤ (towerValue fix 0 h x).val) ∧
    MonoInfl (veblenValue fix pow)

/-- Layer 2: the orbit of `N_B` from `Γ_0` is dominated by its orbit from `0`, shifted by `ω+1`. -/
def OrbitComparison : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    ∀ β γ : CountableOrdinal, γ.val = (ω + 1) + β.val →
      (orbit .base (veblenValue fix pow) (baseValue fix pow w) β).val ≤
        (orbit .base (veblenValue fix pow) zeroValue γ).val

/-- Layer 3: `Calibration` at `n = 2`: `Δ_2' = B_0 N_B Γ_0 = ψ(Ω)`. -/
def CalibrationTwo : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    (sequenceValue fix pow w 2).val = (veblenData fix pow w).psi (actualArgument 2)

end LogicLineages.PersistentMarking.ActualCalibration
