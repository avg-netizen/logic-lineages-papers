module
public import LogicLineages.OrdinalComparison.PeakOrbitDefinitions
public import LogicLineages.OrdinalComparison.PositiveFiniteZerosDefinitions
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.StandardControlCurrent.IdentityTailTargets
open OrdinalComparison

/-- Complete current u:lem:roots with root expanded as exclusion from the literal control range. -/
def RootPeakInjectivity : Prop :=
  ∀ a b : Ordinal.{0}, a < epsilonZero → b < epsilonZero →
    Ordinal.omega0 ≤ a → Ordinal.omega0 ≤ b →
    (actualOrdinalNorm a ∉ Set.range Phi) →
    (actualOrdinalNorm b ∉ Set.range Phi) →
    actualTerminalValue a = actualTerminalValue b → a = b

/-- Complete current u:thm:zeros, retaining actual source AST and effective positive equality enumeration. -/
def EffectiveFiniteZeros : Prop :=
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

end LogicLineages.StandardControlCurrent.IdentityTailTargets
