module
public import LogicLineages.PermittedControl.InverseTableDefinitions
public import LogicLineages.PermittedControl.EntryDefinitions
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- The printed constant `κ_μ = 1 - ⌈N(μ)/2⌉` of the count annotation. -/
noncomputable def countCoreConstant (mu : Ordinal.{0}) : Int :=
  1 - (((actualOrdinalNorm mu + 1) / 2 : Nat) : Int)

/-- Equation (count-core) for a proper interval `(λ, μ)` that is not a
short interval `μ + ω k`. With `η = μ + ω²`, the prefix `(λ, η)` has an
actual first entry with count `i` and norm `q = f^i(x)`; when `λ = η` this
is the identity convention `i = 0`, `q = x`. The actual count `k` of
`(λ, μ)` satisfies `k = f(q)/2 + i + κ_μ`, stated doubled. No entry,
count or funnel hit is supplied as a premise. -/
def CountCore : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (lam mu : Ordinal.{0}) (x : Nat), lam < epsilonZero → Order.IsSuccLimit lam →
    (mu = 0 ∨ Order.IsSuccLimit mu) → mu < lam →
    (¬ ∃ k : Nat, 0 < k ∧ lam = mu + Ordinal.omega0 * (k : Ordinal)) →
    max (actualOrdinalNorm lam) (actualOrdinalNorm mu + 3) ≤ x →
    mu + Ordinal.omega0 ^ (2 : Ordinal.{0}) ≤ lam ∧
    ∃ i k : Nat,
      FirstEntry f (countInitial lam x) (mu + Ordinal.omega0 ^ (2 : Ordinal.{0})) i ∧
      FirstEntry f (countInitial lam x) mu k ∧
      entryNormAt f (countInitial lam x) i = f^[i] x ∧
      2 * (k : Int) = (f (entryNormAt f (countInitial lam x) i) : Int) + 2 * (i : Int) +
        2 * countCoreConstant mu

/-- Equation (zero-replacement). A class of count occurrences
`τ_{P_s}(x_s)` with integer coefficients `a s`, all of whose full values
`f(E_{P_s'}(x_s))` equal one value `C` carrying the ordinary coefficient
`b`, and whose combined leading coefficient vanishes in the integer form
`2b + Σ a = 0`, equals exactly its prefix counts and constants. The counts
and prefix counts are arbitrary actual first-entry counts. -/
def ZeroClassExact : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (n : Nat) (lam mu : Fin n → Ordinal.{0}) (x : Fin n → Nat) (a : Fin n → Int) (b C : Int),
  (∀ s : Fin n, lam s < epsilonZero ∧ Order.IsSuccLimit (lam s) ∧
    (mu s = 0 ∨ Order.IsSuccLimit (mu s)) ∧ mu s < lam s ∧
    (¬ ∃ k : Nat, 0 < k ∧ lam s = mu s + Ordinal.omega0 * (k : Ordinal)) ∧
    max (actualOrdinalNorm (lam s)) (actualOrdinalNorm (mu s) + 3) ≤ x s) →
  2 * b + ∑ s, a s = 0 →
  ∀ (i k : Fin n → Nat),
  (∀ s : Fin n,
    FirstEntry f (countInitial (lam s) (x s)) (mu s + Ordinal.omega0 ^ (2 : Ordinal.{0})) (i s) ∧
    FirstEntry f (countInitial (lam s) (x s)) (mu s) (k s) ∧
    (f (entryNormAt f (countInitial (lam s) (x s)) (i s)) : Int) = C) →
  b * C + ∑ s, a s * (k s : Int) =
    ∑ s, a s * (i s : Int) + ∑ s, a s * countCoreConstant (mu s)

/-- Equal-input prefixes merge: two proper intervals read at the same
input whose actual entry norms coincide have the same actual count. -/
def EqualInputMerge : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (lam mu lam' mu' : Ordinal.{0}) (x : Nat), lam < epsilonZero → lam' < epsilonZero →
    Order.IsSuccLimit lam → Order.IsSuccLimit lam' →
    (mu = 0 ∨ Order.IsSuccLimit mu) → (mu' = 0 ∨ Order.IsSuccLimit mu') →
    mu < lam → mu' < lam' →
    max 2 (max (actualOrdinalNorm lam) (actualOrdinalNorm mu)) ≤ x →
    max 2 (max (actualOrdinalNorm lam') (actualOrdinalNorm mu')) ≤ x →
    ∀ i j : Nat, FirstEntry f (countInitial lam x) mu i →
      FirstEntry f (countInitial lam' x) mu' j →
      entryNormAt f (countInitial lam x) i = entryNormAt f (countInitial lam' x) j → i = j

/-- Input comparison forbids the larger-input prefix from having at least
the larger gap: if `(λ, μ)` read at `y` and `(λ', μ')` read at `x < y`
have equal actual entry norms, then `λ - μ < λ' - μ'`. -/
def DistinctInputGap : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (lam mu lam' mu' : Ordinal.{0}), lam < epsilonZero → lam' < epsilonZero →
    Order.IsSuccLimit lam → Order.IsSuccLimit lam' →
    (mu = 0 ∨ Order.IsSuccLimit mu) → (mu' = 0 ∨ Order.IsSuccLimit mu') →
    mu < lam → mu' < lam' →
    ∀ x y : Nat, gapInputTail lam mu lam' mu' 0 ≤ x → gapInputTail lam mu lam' mu' 0 ≤ y →
      x < y →
      ∀ i j : Nat, FirstEntry f (countInitial lam y) mu i →
        FirstEntry f (countInitial lam' x) mu' j →
        entryNormAt f (countInitial lam y) i = entryNormAt f (countInitial lam' x) j →
        lam - mu < lam' - mu'

/-- Equation (rank-transfer). `Q' = (λ, μ)` is read at `x` and
`P' = (ν + δ, ν)` at `y`, with the smaller gap `δ < λ - μ`. If their
actual entry norms coincide, then `y` is the actual entry norm of
`H = (λ, μ + δ)` at `x`, and the count of `Q'` at `x` is the count of `H`
at `x` plus the count of `P'` at `y`. The tail is the effective
inverse-table tail; no hit, certificate or collision is a premise. -/
def RankTransfer : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (lambda mu nu delta : NONote), Order.IsSuccLimit lambda.1.repr →
  (mu.1.repr = 0 ∨ Order.IsSuccLimit mu.1.repr) →
  (nu.1.repr = 0 ∨ Order.IsSuccLimit nu.1.repr) → Order.IsSuccLimit delta.1.repr →
  mu.1.repr < lambda.1.repr → delta.1.repr < lambda.1.repr - mu.1.repr →
  ∀ x y : Nat, inverseTableTail lambda mu nu delta B ≤ x →
  inverseTableTail lambda mu nu delta B ≤ y →
  ∀ p q : Nat, FirstEntry f (countInitial lambda.1.repr x) mu.1.repr p →
    FirstEntry f (countInitial (nu.1.repr + delta.1.repr) y) nu.1.repr q →
    entryNormAt f (countInitial (nu.1.repr + delta.1.repr) y) q =
      entryNormAt f (countInitial lambda.1.repr x) p →
    ∃ i : Nat, FirstEntry f (countInitial lambda.1.repr x) (mu.1.repr + delta.1.repr) i ∧
      entryNormAt f (countInitial lambda.1.repr x) i = y ∧ p = i + q

/-- Current17 `lem:count-transfer`: exact replacement of a zero class by
prefix counts and constants, merging of equal-input prefixes, and transfer
of a prefix at a larger input to the smaller input. -/
def FullCountTransfer : Prop :=
  CountCore ∧ ZeroClassExact ∧ EqualInputMerge ∧ DistinctInputGap ∧ RankTransfer

end LogicLineages.PermittedControl.Targets
