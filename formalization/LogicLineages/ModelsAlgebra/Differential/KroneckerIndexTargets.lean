module

public import LogicLineages.ModelsAlgebra.Differential.KroneckerIndexDefinitions

@[expose] public section

/-! Exact finite-box arithmetic suppliers for the paper15 higher-order
effective polynomial algorithm. These targets prove actual base-B index/digit
inverse identities and bounds. Arbitrary polynomial substitution is NOT
claimed injective: the actual coordinate box is essential. This component
alone does not close a source statement or an effective decision theorem. -/
namespace LogicLineages.ModelsAlgebra.Differential.Targets

def kroneckerIndexInjective : Prop :=
  ∀ (n B : ℕ), 2 ≤ B → ∀ (d e : Fin n → ℕ),
    KroneckerIndex.Bounded B d → KroneckerIndex.Bounded B e →
    KroneckerIndex.index B d = KroneckerIndex.index B e → d = e

def kroneckerIndexBound : Prop :=
  ∀ (n B : ℕ), 2 ≤ B → ∀ d : Fin n → ℕ, KroneckerIndex.Bounded B d →
    KroneckerIndex.index B d < B ^ n

def kroneckerDigitsBound : Prop :=
  ∀ (n B k : ℕ), 2 ≤ B → KroneckerIndex.Bounded B (KroneckerIndex.digits B n k)

def kroneckerDigitsIndex : Prop :=
  ∀ (n B : ℕ), 2 ≤ B → ∀ d : Fin n → ℕ, KroneckerIndex.Bounded B d →
    KroneckerIndex.digits B n (KroneckerIndex.index B d) = d

def kroneckerIndexDigits : Prop :=
  ∀ (n B k : ℕ), 2 ≤ B → k < B ^ n →
    KroneckerIndex.index B (KroneckerIndex.digits B n k) = k

end LogicLineages.ModelsAlgebra.Differential.Targets
