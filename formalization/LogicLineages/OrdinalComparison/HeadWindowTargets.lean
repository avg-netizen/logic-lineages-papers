module
public import LogicLineages.OrdinalComparison.HeadWindowDefinitions

@[expose] public section

/-! Exact source paper08 lem:head-window (paper.tex906–934), including its
finite-family lexicographic conclusion. All heads/inputs are actual source
ordinals/norm inputs; the next-limit, first-deletion and common-norm suppliers
are conclusions and are not assumed as controller/ordering fields. -/

namespace LogicLineages.OrdinalComparison.Targets

def ActualLeastNextLimit : Prop :=
  ∀ mu lam : Ordinal.{0}, Order.IsSuccLimit lam → mu < lam → mu + Ordinal.omega0 ≤ lam

def ActualNextLimitHeadFacts : Prop :=
  ∀ mu : Ordinal.{0}, mu < epsilonZero → Order.IsSuccLimit mu →
    mu + Ordinal.omega0 < epsilonZero ∧ Order.IsSuccLimit (mu + Ordinal.omega0) ∧
      actualOrdinalNorm (mu + Ordinal.omega0) = actualOrdinalNorm mu + 2 ∧
      ∀ t : Nat, actualOrdinalNorm mu + 2 ≤ t →
        actualDescentStep (actualHeadInitial (mu + Ordinal.omega0) t) = actualHeadInitial mu (Phi t) ∧
        actualHeadEndpoint (mu + Ordinal.omega0) t = actualHeadEndpoint mu (Phi t) ∧
        actualHeadCount (mu + Ordinal.omega0) t = actualHeadCount mu (Phi t) + 1 ∧
        actualHeadValue (mu + Ordinal.omega0) t = actualHeadValue mu (Phi t) + 1

def ActualCommonNormHeadOrder : Prop :=
  ∀ mu lam : Ordinal.{0}, mu < epsilonZero → lam < epsilonZero →
    Order.IsSuccLimit mu → Order.IsSuccLimit lam → mu ≤ lam →
    ∀ t : Nat, actualOrdinalNorm mu ≤ t → actualOrdinalNorm lam ≤ t →
      actualHeadCount mu t ≤ actualHeadCount lam t ∧
      actualHeadEndpoint mu t ≤ actualHeadEndpoint lam t ∧ actualHeadValue mu t ≤ actualHeadValue lam t

def ActualDifferentHeadStrictWindow : Prop :=
  ∀ lam mu : Ordinal.{0}, lam < epsilonZero → mu < epsilonZero →
    Order.IsSuccLimit lam → Order.IsSuccLimit mu → mu < lam →
    ∀ t u : Nat, actualOrdinalNorm lam ≤ t → actualOrdinalNorm mu + 2 ≤ t →
      actualOrdinalNorm mu ≤ u → u < Phi t →
        actualHeadValue mu u < actualHeadValue lam t ∧ actualHeadEndpoint mu u < actualHeadEndpoint lam t

def ActualFiniteHeadWindowLexicographic : Prop :=
  ∀ N : Nat, ∀ lam : Fin N → Ordinal.{0}, ∀ t : Fin N → Nat,
    (∀ i : Fin N, lam i < epsilonZero ∧ Order.IsSuccLimit (lam i)) →
    ∀ s : Nat, (∀ i : Fin N, actualOrdinalNorm (lam i) + 2 ≤ s ∧ s ≤ t i ∧ t i < Phi s) →
      ∀ i j : Fin N,
        (actualHeadValue (lam i) (t i) < actualHeadValue (lam j) (t j) ↔
          actualHeadKeyLess (lam i) (t i) (lam j) (t j)) ∧
        (actualHeadValue (lam i) (t i) = actualHeadValue (lam j) (t j) ↔
          lam i = lam j ∧ t i = t j) ∧
        (actualHeadEndpoint (lam i) (t i) = actualHeadEndpoint (lam j) (t j) ↔
          lam i = lam j ∧ t i = t j)

def FullActualDifferentHeadWindow : Prop :=
  ActualLeastNextLimit ∧ ActualNextLimitHeadFacts ∧ ActualCommonNormHeadOrder ∧
    ActualDifferentHeadStrictWindow ∧ ActualFiniteHeadWindowLexicographic

end LogicLineages.OrdinalComparison.Targets
