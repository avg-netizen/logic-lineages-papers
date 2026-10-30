module
public import LogicLineages.OrdinalComparison.PositiveFiniteZerosDefinitions
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- Entire one-variable finite-zero theorem, with uniform numeric modulus and
exact finite equality enumeration for distinct collected normal forms. -/
def FullActualPositiveFiniteZeros : Prop :=
  Computable₂ encodedPositiveZeroBound ∧ Computable₂ encodedPositiveEqualitySet ∧
  ∀ E F : FixedLimitPositiveExpr,
    fixedLimitProfileBelow epsilonZero E → fixedLimitProfileBelow epsilonZero F →
    let n := positiveExprEncode E
    let m := positiveExprEncode F
    let N := encodedPositiveZeroBound n m
    1≤N ∧
    (collectedPositiveNormalize E=collectedPositiveNormalize F →
      ∀ x : Nat, actualFixedLimitProfileEval E x=actualFixedLimitProfileEval F x) ∧
    (collectedPositiveNormalize E≠collectedPositiveNormalize F →
      (∀ x : Nat, N≤x → actualFixedLimitProfileEval E x≠actualFixedLimitProfileEval F x) ∧
      ∀ x : Nat, 1≤x →
        (actualFixedLimitProfileEval E x=actualFixedLimitProfileEval F x ↔ x∈encodedPositiveEqualitySet n m)) ∧
    (encodedPositiveEqualitySet n m).Nodup ∧
    ∀ x : Nat, x∈encodedPositiveEqualitySet n m ↔
      0<x ∧ x<N ∧ actualFixedLimitProfileEval E x=actualFixedLimitProfileEval F x

end LogicLineages.OrdinalComparison.Targets
