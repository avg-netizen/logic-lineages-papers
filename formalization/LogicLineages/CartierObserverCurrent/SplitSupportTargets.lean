module
public import LogicLineages.CartierObserverCurrent.RootInterpolationDefinitions

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.SplitSupport.Targets
open SplittingRoots RootInterpolation

/-- Exact multiset, so no hidden multiplicities or missing roots. -/
def ProductRoots : Prop := ∀ d : Nat,
  (rootProduct d).roots = (SplittingRoots.rootSet d).val

/-- Splitting is explicit here, never inferred from vacuous finite-field root tests. -/
def SplitDivisibility : Prop := ∀ d : Nat, ∀ Q : Polynomial (FieldAt d), Q ≠ 0 → Q.Splits →
  (Q ∣ rootProduct d ↔
    (∀ z : FieldAt d, Q.eval z = 0 → z ∈ SplittingRoots.rootSet d) ∧
    (∀ z : FieldAt d, Q.rootMultiplicity z ≤ 1))

/-- Actual source divisibility supplies the splitting required in the preceding target. -/
def SourceSimpleDivisor : Prop := ∀ d : Nat, ∀ Q : Polynomial (FieldAt d), Q ≠ 0 →
  Q ∣ splitPolynomial d → (∀ z : FieldAt d, Q.rootMultiplicity z ≤ 1) → Q ∣ rootProduct d
end LogicLineages.CartierObserverCurrent.SplitSupport.Targets
