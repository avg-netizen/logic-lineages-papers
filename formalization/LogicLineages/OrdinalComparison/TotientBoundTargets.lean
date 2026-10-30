module
public import Mathlib.Data.Nat.Totient

@[expose] public section

/-! Source paper10 lem:bounds, paper.tex580–591: exact Euler-totient lower
bound for the actual Fermat-shaped composite modulus. The strict bound is
cross-multiplied by r+1>0, not weakened by integer truncation of a quotient.
The other linked-input/exponential-gap clauses remain separate obligations. -/

namespace LogicLineages.OrdinalComparison.Targets

def ActualTotientPrimeFactorBound : Prop :=
  ∀ n : Nat, 0 < n → n ≤ (n.primeFactors.card + 1) * Nat.totient n

def ActualFermatShapeTotientLowerBound : Prop :=
  ∀ r : Nat, 0 < r → 2 ^ r < (r + 1) * Nat.totient (2 ^ r + 1)

end LogicLineages.OrdinalComparison.Targets
