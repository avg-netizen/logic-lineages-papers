module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationTargets
public import LogicLineages.PersistentMarking.ActualOmegaTowerProof
public import LogicLineages.NativeModule.PersistentMarking.ActualCollapseCriticalProof

@[expose] public section

/-! # Calibration at n = 3: statements (frozen before proof)

`D β := B_0^β(N_B)` (the `A_1`-orbit of `B_0` from `N_B`), `L α := D α 0`, and
`Δ_3' = B_1 B_0 N_B Γ_0 = fix L Γ_0`. On the ψ side, `Ω^e` for countable `e` is the index
`powerIndex e`. -/

namespace LogicLineages.PersistentMarking.ActualCalibrationThree
open Ordinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalNativeIterationTargets OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets
open NativeTowerTargets NativeTowerSequenceTargets ActualCollapse ActualCalibration
open scoped Ordinal

/-- The levels `D β = B_0^β(N_B)`. -/
noncomputable def level (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (pow : CountableOrdinal → CountableOrdinal) (β : CountableOrdinal) : CountableOrdinal → CountableOrdinal :=
  orbit (tier 1) (towerValue fix 0) (veblenValue fix pow) β

/-- `Ω^e` as an index (`e` countable, so `Ω^e ≤ Ω^Ω = a_3 ≤ Λ`). -/
noncomputable def powerIndex (e : CountableOrdinal) : ActualIndex :=
  ⟨omegaIndex ^ e.val,
    (Ordinal.opow_le_opow_right (zero_lt_one.trans one_lt_index)
      (show e.val ≤ omegaIndex from (countable_val_lt e).le)).trans
      (le_of_eq_of_le
        ((exact_LiteralRecurrence.2.2.2.2 2).trans (congrArg (omegaIndex ^ ·) exact_LiteralRecurrence.2.2.2.1)).symm
        (Ordinal.le_iSup (fun m => argument m) 3))⟩

/-- T1 (generic): for a monotone, weakly inflationary `g` continuous at limits, `fix g x` is the
least fixed point of `g` strictly above `x`. -/
def FixLeastAbove : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    ∀ g : CountableOrdinal → CountableOrdinal,
      (∀ x y : CountableOrdinal, x.val ≤ y.val → (g x).val ≤ (g y).val) →
      (∀ x, x.val ≤ (g x).val) →
      (∀ l : CountableOrdinal, Order.IsSuccLimit l.val →
        (g l).val = ⨆ e : EarlierStages l, (g (earlierStage l e)).val) →
      ∀ x : CountableOrdinal,
        g (fix g x) = fix g x ∧ x.val < (fix g x).val ∧
        ∀ θ : CountableOrdinal, x.val < θ.val → g θ = θ → (fix g x).val ≤ θ.val

/-- T2 (the reusable `B_0` lemma): for monotone inflationary `h` with `ω² ≤ h(ω)`, `B_0 h (h ω)`
is the least fixed point of `α ↦ h^α(h ω)`. -/
def B0Lemma : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    ∀ h : CountableOrdinal → CountableOrdinal, MonoInfl h → (ω : Ordinal.{0}) ^ (2 : Ordinal.{0}) ≤ (h w).val →
      (orbit .base h (h w) (towerValue fix 0 h (h w))).val = (towerValue fix 0 h (h w)).val ∧
      ∀ θ : CountableOrdinal, θ.val < (towerValue fix 0 h (h w)).val → θ.val < (orbit .base h (h w) θ).val

/-- T3 (level-1 helpfulness invariant, semantic): every level is monotone inflationary, the
levels increase pointwise, and `D (β+1) x` is the least fixed point above `x` of the level-β
enumeration `α ↦ (D β)^α(0)` ("`B_0` sends each level-enumeration to the next level"). -/
def LevelInvariant : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    (∀ β, MonoInfl (level fix pow β)) ∧
    (∀ α β : CountableOrdinal, α.val ≤ β.val → ∀ x, (level fix pow α x).val ≤ (level fix pow β x).val) ∧
    ∀ β β' : CountableOrdinal, β'.val = β.val + 1 → ∀ x : CountableOrdinal,
      let E := fun α => orbit .base (level fix pow β) zeroValue α
      E (level fix pow β' x) = level fix pow β' x ∧ x.val < (level fix pow β' x).val ∧
      ∀ θ : CountableOrdinal, x.val < θ.val → E θ = θ → (level fix pow β' x).val ≤ θ.val

/-- T4 (ψ on `[Ω, Ω^Ω)`, at the powers): below the least fixed point of `L`, `ψ(Ω^e) = L e`
for `e ≥ 1`. -/
def PsiPowerLevel : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    ∀ e : CountableOrdinal, 1 ≤ e.val →
      (∀ θ : CountableOrdinal, 1 ≤ θ.val → θ.val ≤ e.val → level fix pow θ zeroValue ≠ θ) →
      (veblenData fix pow w).psi (powerIndex e) = (level fix pow e zeroValue).val

/-- T5: `Calibration` at `n = 3`. -/
def CalibrationThree : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    (sequenceValue fix pow w 3).val = (veblenData fix pow w).psi (actualArgument 3)

end LogicLineages.PersistentMarking.ActualCalibrationThree
