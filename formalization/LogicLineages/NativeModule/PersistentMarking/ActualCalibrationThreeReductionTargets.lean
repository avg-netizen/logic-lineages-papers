module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationThreeTargets

@[expose] public section

/-! # Calibration at n = 3 from the collapse at the powers of Ω (T4 ⟹ T5)

Frozen before proof (local Fable-trio round, 27 November 2026, root lane).

`L α := D α 0 = B_0^α(N_B)(0)`. The statements say that `Δ_3' = ψ(Ω^Ω)` follows from the frozen T4
(`ActualCalibrationThree.PsiPowerLevel`) and two facts about `L` alone: it is strictly increasing,
and `Γ_0 < L e` for `e ≥ 1`. Neither T4 nor those two facts is asserted here. -/

namespace LogicLineages.PersistentMarking.ActualCalibrationThreeReduction
open Ordinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualCalibration ActualCalibrationThree
open scoped Ordinal

/-- `L` is strictly increasing. -/
def LevelZeroStrict (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (pow : CountableOrdinal → CountableOrdinal) : Prop :=
  ∀ α β : CountableOrdinal, α.val < β.val →
    (level fix pow α zeroValue).val < (level fix pow β zeroValue).val

/-- `Γ_0 < L e` for `e ≥ 1`. -/
def BaseBelowLevel (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (pow : CountableOrdinal → CountableOrdinal) (w : CountableOrdinal) : Prop :=
  ∀ e : CountableOrdinal, 1 ≤ e.val → (baseValue fix pow w).val < (level fix pow e zeroValue).val

/-- T4 at one solution of the equations. -/
def PsiPowerLevelAt (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (pow : CountableOrdinal → CountableOrdinal) (w : CountableOrdinal) : Prop :=
  ∀ e : CountableOrdinal, 1 ≤ e.val →
    (∀ θ : CountableOrdinal, 1 ≤ θ.val → θ.val ≤ e.val → level fix pow θ zeroValue ≠ θ) →
    (veblenData fix pow w).psi (powerIndex e) = (level fix pow e zeroValue).val

/-- The powers `Ω^e` lie below `Ω^Ω = a_3`, have norm at most `e` (for `e ≥ 1`), and every index
below `Ω^Ω` with norm below `e` lies below `Ω^e`. -/
def PowerIndexFacts : Prop :=
  (∀ e : CountableOrdinal, powerIndex e < actualArgument 3) ∧
  (∀ e : CountableOrdinal, 1 ≤ e.val → actualNorm (powerIndex e) ≤ e.val) ∧
  (∀ η : ActualIndex, η < actualArgument 3 → ∀ e : CountableOrdinal, 1 ≤ e.val →
    actualNorm η < e.val → η < powerIndex e)

/-- The n = 3 instance at one solution, from the two facts about `L` and T4 there. -/
def ThreeFromLevelFacts : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    LevelZeroStrict fix pow → BaseBelowLevel fix pow w → PsiPowerLevelAt fix pow w →
    (sequenceValue fix pow w 3).val = (veblenData fix pow w).psi (actualArgument 3)

/-- The two facts about `L`, for every solution. -/
def LevelFacts : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    LevelZeroStrict fix pow ∧ BaseBelowLevel fix pow w

/-- T4 ⟹ T5, given the two facts about `L`. -/
def ThreeFromPower : Prop := LevelFacts → PsiPowerLevel → CalibrationThree

end LogicLineages.PersistentMarking.ActualCalibrationThreeReduction
