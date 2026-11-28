module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationStepOrbitTargets

@[expose] public section

/-! # The calibration at every type level: the function side (frozen before proof)

Local Fable-trio round, 27 November 2026, lane Fable A2. Plan and paper checks:
`verification/local-fable-trio-2026-11-27/fableA2/UNIFORM-INDUCTION-PLAN.md`.

The hereditary notion of a *good* object of type `A_{k+1}` is stated in flat (environment) form:
`F : A_{k+1}` is good when, for every environment `xs` whose slots `k, …, 1` hold good objects of
types `A_k, …, A_1`, the fully applied function `appDown k F xs = F (xs k) ⋯ (xs 1) : A_1` is a good
function (`GoodFn`) and lies pointwise above `B_0` of the first argument applied down (`domClause`).
At `k = 0` this is `GoodFn`; at `k = 1` it is `GoodOp` of the level-2 targets.

Statements:
- `FamilyDiagonal`: for a family `K a : A_1` (`a` countable) of good functions with
  `B_0 (K a) ≤ K (a+1)` pointwise and pointwise suprema at limits: monotone and strictly increasing
  in `a`, `a ≤ K a 0`, the fixed points of `a ↦ K a 0` are limits closed under the family and
  critical above `Γ_0`, and `fix (a ↦ K a 0)` is a good function, least-fixed-point above its
  argument, strictly above `B_0 (K a)` for small `a`;
- `OrbitGood`: orbits of a good object from a good object are good, at every type;
- `TowerGood`: every `B_m` is good.

Nothing here mentions the collapse. -/

namespace LogicLineages.PersistentMarking.ActualCalibrationUniform
open Ordinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualCalibration ActualCalibrationThree
open ActualCalibrationStep
open scoped Ordinal

/-- Apply `v : A_{k+1}` to the slots `k, k-1, …, 1`. -/
def appDown : (k : Nat) → Value (tier (k + 1)) → Env → CountableOrdinal → CountableOrdinal
  | 0, v, _ => v
  | k + 1, v, xs => appDown k (v (xs (k + 1))) xs

/-- After applying down, `F` lies pointwise above `B_0` of its first argument applied down. -/
def domClause (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal) :
    (k : Nat) → Value (tier (k + 1)) → Env → Prop
  | 0, _, _ => True
  | k + 1, F, xs => ∀ x : CountableOrdinal,
      (towerValue fix 0 (appDown k (xs (k + 1)) xs) x).val ≤ (appDown (k + 1) F xs x).val

/-- `F : A_{k+1}` is good relative to the environments in `E`. -/
def GoodAt (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (pow : CountableOrdinal → CountableOrdinal) (w : CountableOrdinal) (k : Nat) (E : Env → Prop)
    (F : Value (tier (k + 1))) : Prop :=
  ∀ xs : Env, E xs → GoodFn fix pow w (appDown k F xs) ∧ domClause fix k F xs

/-- The slots `1, …, k` of the environment hold good objects. -/
def GoodEnv (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (pow : CountableOrdinal → CountableOrdinal) (w : CountableOrdinal) : Nat → Env → Prop
  | 0 => fun _ => True
  | k + 1 => fun xs =>
      GoodEnv fix pow w k xs ∧ GoodAt fix pow w k (GoodEnv fix pow w k) (xs (k + 1))

/-- `F : A_{k+1}` is good. -/
def GoodF (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (pow : CountableOrdinal → CountableOrdinal) (w : CountableOrdinal) (k : Nat)
    (F : Value (tier (k + 1))) : Prop :=
  GoodAt fix pow w k (GoodEnv fix pow w k) F

/-- A family of good functions with `B_0 (K a) ≤ K (a+1)` and pointwise suprema at limits. -/
def GoodFamily (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (pow : CountableOrdinal → CountableOrdinal) (w : CountableOrdinal)
    (K : CountableOrdinal → CountableOrdinal → CountableOrdinal) : Prop :=
  (∀ a : CountableOrdinal, GoodFn fix pow w (K a)) ∧
  (∀ a a' : CountableOrdinal, a'.val = a.val + 1 → ∀ x : CountableOrdinal,
    (towerValue fix 0 (K a) x).val ≤ (K a' x).val) ∧
  (∀ l : CountableOrdinal, Order.IsSuccLimit l.val → ∀ x : CountableOrdinal,
    (K l x).val = ⨆ e : EarlierStages l, (K (earlierStage l e) x).val)

/-- The function-side facts about a good family and its diagonal fixed points. -/
def FamilyDiagonal : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    ∀ K : CountableOrdinal → CountableOrdinal → CountableOrdinal, GoodFamily fix pow w K →
      (∀ a b x : CountableOrdinal, a.val ≤ b.val → (K a x).val ≤ (K b x).val) ∧
      (∀ a a' x : CountableOrdinal, a'.val = a.val + 1 → (K a x).val < (K a' x).val) ∧
      (∀ a : CountableOrdinal, a.val ≤ (K a zeroValue).val) ∧
      (∀ κ : CountableOrdinal, K κ zeroValue = κ → 0 < κ.val →
        Order.IsSuccLimit κ.val ∧
        ∀ a x : CountableOrdinal, a.val < κ.val → x.val < κ.val → (K a x).val < κ.val) ∧
      (∀ κ : CountableOrdinal, K κ zeroValue = κ → (baseValue fix pow w).val < κ.val →
        Critical (veblenValue fix pow) (baseValue fix pow w) κ.val) ∧
      (∀ x : CountableOrdinal,
        K (fix (fun a => K a zeroValue) x) zeroValue = fix (fun a => K a zeroValue) x ∧
        x.val < (fix (fun a => K a zeroValue) x).val ∧
        ∀ θ : CountableOrdinal, x.val < θ.val → K θ zeroValue = θ →
          (fix (fun a => K a zeroValue) x).val ≤ θ.val) ∧
      GoodFn fix pow w (fix (fun a => K a zeroValue)) ∧
      ∀ a x : CountableOrdinal, a.val < (fix (fun a => K a zeroValue) x).val →
        (towerValue fix 0 (K a) x).val < (fix (fun a => K a zeroValue) x).val

/-- Orbits of a good object from a good object are good. -/
def OrbitGood : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    ∀ (k : Nat) (Ψ : Value (tier (k + 2))) (Φ : Value (tier (k + 1))),
      GoodF fix pow w (k + 1) Ψ → GoodF fix pow w k Φ →
      ∀ a : CountableOrdinal, GoodF fix pow w k (orbit (tier (k + 1)) Ψ Φ a)

/-- Every `B_m` is good. -/
def TowerGood : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    ∀ m : Nat, GoodF fix pow w (m + 1) (towerValue fix m)

end LogicLineages.PersistentMarking.ActualCalibrationUniform
