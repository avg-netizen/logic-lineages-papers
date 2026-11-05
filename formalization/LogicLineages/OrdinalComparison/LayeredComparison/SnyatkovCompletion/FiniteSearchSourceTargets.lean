module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchSourceDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchSourceTargets
open CommonLayerSyntax FiniteSearchSource

def SupplierInclusion : Prop :=
  (∀ p : SourceFormula, ScopedPhiParameters.test [] p = true → test p = true) ∧
  (∀ p : SourceFormula, BoundedSource.test p = true → test p = true)

def ActualTruth : Prop := ∀ (values : List Nat) (p : SourceFormula), test p = true →
  (answer values p = true ↔ p.eval (PlainParameterDecision.valuation values))

def ActualDecision : Prop := ∀ (values : List Nat) (p : SourceFormula),
  (FiniteSearchSource.decide values p).isSome = test p ∧
  (test p = true → ∀ b : Bool, FiniteSearchSource.decide values p = some b ↔
    (p.eval (PlainParameterDecision.valuation values) ↔ b = true))

def ActiveEnvironmentSearch : Prop := ∀ (values : List Nat) (i : Nat) (p : SourceFormula) (t : BaseTerm),
  ScopedPhiParameters.test [] (.existsNat i p) = false → BoundedSource.guard i p = some t →
  answer values (.existsNat i p) =
    (List.range (t.value (PlainParameterDecision.valuation values))).any (fun n =>
      answer (BoundedSourcePrograms.Code.update values i n) p)

def MixedBoundedUnbounded : Prop := ∀ (i j : Nat) (bound : BaseTerm),
  i ≠ j → i ∉ bound.variables → test (boundedOuter i j bound) = true ∧
  ∀ values : List Nat, FiniteSearchSource.decide values (boundedOuter i j bound) = some true ↔
    0 < bound.value (PlainParameterDecision.valuation values)

def UnboundedNonlinearBoundary : Prop := ∀ i : Nat,
  test (.existsNat i (.equal (.phi (.variable i)) (.variable i))) = false

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchSourceTargets
