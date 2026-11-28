module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationStepOrbitTargets

@[expose] public section

/-! # Level 2 of the calibration: statements (frozen before proof)

`levelTwo fix e = B_1^e B_0` (tier-2 orbit of `B_1` from `B_0`); root's level diagonal at level 2
is `e ↦ levelTwo fix e N_B 0`. Statements:

- `OpSuccessor`: `B_1` maps a good type-2 operator `G` (good functions to good functions, and
  `B_0 K ≤ G K` pointwise) to a good operator, strictly above `G`;
- `LevelTwoGood`: every `levelTwo fix e` is a good operator, monotone and strictly increasing in `e`;
- `OpWeightSuccessor`: if `G` adds `Ω^e` to the exponent of every step (`IsStep ε H → IsStep (ε + Ω^e) (G H)`
  in exponent contexts `ExpCond ε e`), then `B_1 G` adds `Ω^(e+1)`;
- `LevelTwoWeight`: `levelTwo fix e` adds `Ω^e` to the exponent of every step.

Nothing is asserted here about the collapse at `Ω^(Ω^e)` itself or about higher types. -/

namespace LogicLineages.PersistentMarking.ActualCalibrationStep
open Ordinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualCalibration ActualCalibrationThree
open scoped Ordinal

/-- `B_1^e B_0`. -/
noncomputable def levelTwo (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (e : CountableOrdinal) :
    (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal :=
  orbit (tier 2) (towerValue fix 1) (towerValue fix 0) e

/-- A good type-2 operator: good functions to good functions, pointwise above `B_0`. -/
def GoodOp (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (pow : CountableOrdinal → CountableOrdinal) (w : CountableOrdinal)
    (G : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal) : Prop :=
  ∀ K : CountableOrdinal → CountableOrdinal, GoodFn fix pow w K →
    GoodFn fix pow w (G K) ∧ ∀ x : CountableOrdinal, (towerValue fix 0 K x).val ≤ (G K x).val

/-- An admissible exponent context for adding `Ω^s`. -/
def ExpCond (ε s : Ordinal.{0}) : Prop :=
  NormSeparated ε s ∧
  coefficientNorm ε ≤ coefficientNorm (ε + omegaIndex ^ s) ∧
  s ≤ coefficientNorm (ε + omegaIndex ^ s) ∧
  omegaIndex ^ (ε + omegaIndex ^ s) < endpoint

/-- `B_1` preserves good operators and is strictly above its argument. -/
def OpSuccessor : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    ∀ G : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal,
      GoodOp fix pow w G →
      GoodOp fix pow w (towerValue fix 1 G) ∧
      ∀ K : CountableOrdinal → CountableOrdinal, GoodFn fix pow w K → ∀ x : CountableOrdinal,
        (G K x).val < (towerValue fix 1 G K x).val

/-- The operators `B_1^e B_0` are good, monotone and strictly increasing in `e`. -/
def LevelTwoGood : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    (∀ e : CountableOrdinal, GoodOp fix pow w (levelTwo fix e)) ∧
    (∀ (e e' : CountableOrdinal) (K : CountableOrdinal → CountableOrdinal), GoodFn fix pow w K →
      e.val ≤ e'.val → ∀ x : CountableOrdinal, (levelTwo fix e K x).val ≤ (levelTwo fix e' K x).val) ∧
    (∀ (e e' : CountableOrdinal) (K : CountableOrdinal → CountableOrdinal), GoodFn fix pow w K →
      e'.val = e.val + 1 → ∀ x : CountableOrdinal,
        (levelTwo fix e K x).val < (levelTwo fix e' K x).val)

/-- If `G` adds `Ω^e` to the exponent of every step, `B_1 G` adds `Ω^(e+1)`. -/
def OpWeightSuccessor : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    ∀ (G : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
      (e e' : CountableOrdinal), e'.val = e.val + 1 → GoodOp fix pow w G →
      (∀ (ε : Ordinal.{0}) (H : CountableOrdinal → CountableOrdinal), ExpCond ε e.val →
        IsStep fix pow w ε H → IsStep fix pow w (ε + omegaIndex ^ e.val) (G H)) →
      ∀ (ε : Ordinal.{0}) (H : CountableOrdinal → CountableOrdinal), ExpCond ε e'.val →
        IsStep fix pow w ε H →
        IsStep fix pow w (ε + omegaIndex ^ e'.val) (towerValue fix 1 G H)

/-- `B_1^e B_0` adds `Ω^e` to the exponent of every step. -/
def LevelTwoWeight : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    ∀ (e : CountableOrdinal) (ε : Ordinal.{0}) (H : CountableOrdinal → CountableOrdinal),
      ExpCond ε e.val → IsStep fix pow w ε H →
      IsStep fix pow w (ε + omegaIndex ^ e.val) (levelTwo fix e H)

end LogicLineages.PersistentMarking.ActualCalibrationStep
