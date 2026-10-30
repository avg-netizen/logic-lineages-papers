module

public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-! Literal bounded-base exponent encoding used by the existing paper15
spectral decision programme. This is ordinary base-B arithmetic, with no
injectivity, inverse-digit or polynomial interpretation oracle. -/
namespace LogicLineages.ModelsAlgebra.Differential.KroneckerIndex

def index (B : ℕ) {n : ℕ} (d : Fin n → ℕ) : ℕ :=
  ∑ i : Fin n, d i * B ^ i.val

def digits (B n k : ℕ) : Fin n → ℕ :=
  fun i => (k / B ^ i.val) % B

def Bounded (B : ℕ) {n : ℕ} (d : Fin n → ℕ) : Prop :=
  ∀ i, d i < B

end LogicLineages.ModelsAlgebra.Differential.KroneckerIndex
