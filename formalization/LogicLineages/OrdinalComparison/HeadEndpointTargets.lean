module
public import LogicLineages.OrdinalComparison.HeadEndpointDefinitions

@[expose] public section

/-! Independent full source contracts: paper10 prop:complete and paper08
lem:endpoints. The head input uses total norm t, every actual ordinal endpoint
is the original evaluator endpoint, and termination is the literal corrected
ordinal-step trace. No monotonicity, range/spacing or count identity is a premise. -/

namespace LogicLineages.OrdinalComparison.Targets

def ActualHeadInputFacts : Prop :=
  ∀ lam : Ordinal.{0}, lam < epsilonZero → Order.IsSuccLimit lam →
    ∀ t : Nat, actualOrdinalNorm lam ≤ t →
      actualHeadInitial lam t < epsilonZero ∧ Ordinal.omega0 ≤ actualHeadInitial lam t ∧
        actualOrdinalNorm (actualHeadInitial lam t) = t

def ActualNonfiniteNormLowerBound : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero → Ordinal.omega0 ≤ a → 2 ≤ actualOrdinalNorm a

def ActualHeadCompleteCount : Prop :=
  ∀ lam : Ordinal.{0}, lam < epsilonZero → Order.IsSuccLimit lam →
    ∀ t : Nat, actualOrdinalNorm lam ≤ t →
      actualControlledCount Phi (actualHeadInitial lam t) = actualHeadCount lam t ∧
      0 < actualHeadCount lam t ∧
      actualControlledStateAfter Phi (actualHeadInitial lam t) (actualHeadCount lam t) =
        (actualHeadEndpoint lam t : Ordinal) ∧
      (∀ i : Nat, i < actualHeadCount lam t →
        Ordinal.omega0 ≤ actualControlledStateAfter Phi (actualHeadInitial lam t) i) ∧
      actualHeadEndpoint lam t = (Phi^[actualHeadCount lam t]) t ∧
      actualHeadValue lam t = actualHeadEndpoint lam t + actualHeadCount lam t

def FullActualHeadCompleteCount : Prop := ActualHeadInputFacts ∧ ActualHeadCompleteCount

def ActualFixedHeadValueEndpointOrder : Prop :=
  ∀ lam : Ordinal.{0}, lam < epsilonZero → Order.IsSuccLimit lam →
    ∀ t u : Nat, actualOrdinalNorm lam ≤ t → actualOrdinalNorm lam ≤ u → t < u →
      actualHeadValue lam t < actualHeadValue lam u ∧ actualHeadEndpoint lam t < actualHeadEndpoint lam u

def ActualDistinctEndpointExponentialGap : Prop :=
  ∀ a b : Ordinal.{0}, a < epsilonZero → b < epsilonZero → Ordinal.omega0 ≤ a → Ordinal.omega0 ≤ b →
    actualTerminalValue a < actualTerminalValue b →
      2 ^ (actualTerminalValue a + 1) ≤ actualTerminalValue b

def ActualInfiniteValueEndpointBand : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero → Ordinal.omega0 ≤ a →
    let s := (Phi^[actualReplacementCount a - 1]) (actualOrdinalNorm a)
    let Z := actualTerminalValue a
    Z = Phi s ∧ Z < actualCollapse a ∧ actualCollapse a < 2 * Z ∧ 2 * Z < Phi (s + 1)

def FullActualSparseEndpointComparison : Prop :=
  ActualNonfiniteNormLowerBound ∧ ActualFixedHeadValueEndpointOrder ∧
    ActualDistinctEndpointExponentialGap ∧ ActualInfiniteValueEndpointBand

end LogicLineages.OrdinalComparison.Targets
