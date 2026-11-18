module
public import LogicLineages.CartierObserverCurrent.SourceBudgetDefinitions
public import LogicLineages.CartierObserverCurrent.NaturalityDefinitions
public import Mathlib.Algebra.Polynomial.Div

@[expose] public section
universe u v
namespace LogicLineages.CartierObserverCurrent.SourceBudget.Targets

def SourceConstant : Prop :=
  ∀ (K : Type u) [Field K], ∀ d : Nat, (denominator K d).coeff 0 = 1

def SourceMap : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L], ∀ σ : K →+* L, ∀ d : Nat,
    (denominator K d).map σ = denominator L d

def BinomialMultiplicity : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2], ∀ n : Nat, 0 < n → ∀ z : K,
    (1 + Polynomial.X ^ n : Polynomial K).rootMultiplicity z ≤ 2 ^ padicValNat 2 n

def SourceMultiplicity : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2], ∀ d : Nat, ∀ z : K,
    (denominator K d).rootMultiplicity z ≤ budget d

def PositiveBudgetTransient : Prop :=
  ∀ d : Nat, 1 ≤ d → 0 < budget d ∧ budget d ≤ 2 ^ transient d

def MappedProperInput : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L], ∀ σ : K →+* L,
    ∀ d : Nat, ∀ P : Polynomial K, P.degree < (denominator K d).degree →
      (P.map σ).degree < (denominator L d).degree ∧
      Naturality.rationalMap σ
        (algebraMap (Polynomial K) (RatFunc K) P /
          algebraMap (Polynomial K) (RatFunc K) (denominator K d)) =
        algebraMap (Polynomial L) (RatFunc L) (P.map σ) /
          algebraMap (Polynomial L) (RatFunc L) (denominator L d) ∧
      MixedProper.proper
        (algebraMap (Polynomial L) (RatFunc L) (P.map σ) /
          algebraMap (Polynomial L) (RatFunc L) (denominator L d))
end LogicLineages.CartierObserverCurrent.SourceBudget.Targets
