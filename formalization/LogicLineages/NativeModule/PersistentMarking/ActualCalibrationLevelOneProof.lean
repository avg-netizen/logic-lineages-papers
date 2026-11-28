module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationThreePowerProof
public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationLevelsTargets

@[expose] public section

/-! The per-level interface `ActualCalibrationLevels` is instantiable at level 1: its level
diagonal is `L = (β ↦ D β 0)`, `LevelFactsAt 1` is strict T3 + `Γ_0 < L e` + the limit clause,
and `PsiTowerLevelAt 1` is T4 (`psiPowerLevel`), the index `⟨Ω^e, h⟩` being `powerIndex e`. -/

namespace LogicLineages.PersistentMarking.ActualCalibrationThree
open Ordinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualCalibrationLevels
open scoped Ordinal

theorem levelDiagonal_one (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (pow : CountableOrdinal → CountableOrdinal) (α : CountableOrdinal) :
    levelDiagonal fix pow 1 α = level fix pow α zeroValue := rfl

theorem levelFactsAt_one (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) : LevelFactsAt fix pow w 1 :=
  ⟨fun α β h => levelZero_strict h1 h2 α β h, fun e he => base_lt_level h1 h2 e he,
    fun l hl => level_limit l hl zeroValue⟩

theorem psiTowerLevelAt_one (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (h1 : OrdinalArithmeticEquations Z s add mul)
    (h2 : OmegaArithmeticEquations Z s mul w one pow fix) : PsiTowerLevelAt fix pow w 1 := by
  intro e he1 hnofix h
  exact psiPowerLevel Z s add mul w one pow fix h1 h2 e he1 hnofix

#print axioms levelFactsAt_one
#print axioms psiTowerLevelAt_one

end LogicLineages.PersistentMarking.ActualCalibrationThree
