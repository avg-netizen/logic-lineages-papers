module

public import LogicLineages.NativeModule.PersistentMarking.ActualCollapseDefinitions

@[expose] public section

namespace LogicLineages.PersistentMarking.ActualCollapse
open Ordinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets
open OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets NativeTowerTargets NativeTowerSequenceTargets
open scoped Ordinal

/-! Norm layer. -/

/-- "In particular |a_n| ≤ 1." -/
def NormBound : Prop := ∀ n, coefficientNorm (argument n) ≤ 1

/-- Norms are countable ordinals. -/
def NormBelowOmegaOne : Prop := ∀ o : Ordinal.{0}, coefficientNorm o < ω₁

/-- Below `Λ`, only countably many ordinals have norm below a countable `θ`. -/
def NormCountable : Prop :=
  ∀ θ : Ordinal.{0}, θ < ω₁ → Set.Countable {η : Ordinal.{0} | η < endpoint ∧ coefficientNorm η < θ}

/-! Criticality layer, for an inflationary `N` with `1 < Γ`. -/

def Inflationary (N : CountableOrdinal → CountableOrdinal) : Prop := ∀ x, x.val < (N x).val

def CriticalFacts : Prop :=
  ∀ (N : CountableOrdinal → CountableOrdinal) (Γ : CountableOrdinal), Inflationary N → 1 < Γ.val →
    (∀ θ, Critical N Γ θ → 1 < θ) ∧ (∀ θ, Critical N Γ θ → θ < ω₁) ∧
    (∀ β, β < ω₁ → ∃ θ, Critical N Γ θ ∧ β < θ) ∧
    (∀ f : ℕ → Ordinal.{0}, StrictMono f → (∀ n, Critical N Γ (f n)) →
      ∀ θ, IsLUB (Set.range f) θ → Critical N Γ θ)

/-- The paper's `N_B` is strictly inflationary ("the strictly inflationary function N_B") and
`Γ_0 = N_B(ω) > 1`. -/
def VeblenInflationary : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    Inflationary (veblenValue fix pow) ∧ 1 < (baseValue fix pow w).val

/-! (P) and the tower. -/

/-- (P) holds for the recursively defined collapse. -/
def ActualCharacterization : Prop :=
  ∀ (N : CountableOrdinal → CountableOrdinal) (Γ : CountableOrdinal), Inflationary N → 1 < Γ.val →
    CharacterizationP (actualData N Γ)

/-- All of `TowerHypotheses` for the paper's actual data. -/
def ActualTowerHypotheses : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    TowerHypotheses (veblenData fix pow w)

/-- `lem:tower-cofinality`'s first equality for the actual data: `sup_n ψ_B(a_n) = ψ_B(Λ)`. -/
def ActualTowerSupremum : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    (⨆ n, (veblenData fix pow w).psi (actualArgument n)) = (veblenData fix pow w).psi actualEndpoint

end LogicLineages.PersistentMarking.ActualCollapse
