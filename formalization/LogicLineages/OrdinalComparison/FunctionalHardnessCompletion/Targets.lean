module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.Targets
open SourcePolynomialRealization SourceFiniteExponentProjection OriginalDomain

def CompletePatterns : Prop := ∀ n : Nat,
  (masks n).length = 2^n ∧ ∀ z : Mask n, z ∈ masks n

def ExactRestriction : Prop := ∀ (n : Nat) (z : Mask n),
  (∀ (x : Fin n → Ordinal) (d : SignedPair.Expression n),
    SignedPair.meaning x (restrict z d) = SignedPair.meaning (zeroExtend z x) d) ∧
  (∀ (x : Fin n → PolynomialGroup) (d : SignedPair.Expression n),
    polynomialMeaning x (restrict z d) = polynomialMeaning (zeroExtend z x) d)

def SimultaneousPolynomialPatterns : Prop := ∀ (n : Nat) (s : System n),
  PolynomialSatisfiable s ↔
    ∃ z ∈ masks n, ∃ p : Fin n → NonnegativePolynomial,
      (∀ i, p i ≠ 0) ∧ PolynomialSolves (restrictSystem z s) p

/-- No polynomial nonzero side condition remains in the original problem.
The right hand side uses genuine admissible substitutions and one shared
valuation for the entire system. All 2^n executable patterns are covered. -/
def SimultaneousActualPatterns : Prop := ∀ (n : Nat) (s : System n),
  PolynomialSatisfiable s ↔ PatternOrdinalSatisfiable s

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.Targets
