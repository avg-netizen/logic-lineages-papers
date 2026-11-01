module
public import LogicLineages.OrdinalComparison.HeadWindowTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- Exact whole-genuine-domain upward identity from source09 head-graph proof.
Actual ordinal heads and actual collapse/terminal/count functions are retained;
no eventual-only qualification or graph/shift/decomposition oracle is assumed. -/
def ActualFiniteOmegaHeadShift : Prop :=
  ∀ beta : Ordinal.{0}, beta < epsilonZero → Order.IsSuccLimit beta → ∀ delta : Nat,
    let xi := beta + Ordinal.omega0 * (delta : Ordinal)
    xi < epsilonZero ∧ Order.IsSuccLimit xi ∧
      actualOrdinalNorm xi = actualOrdinalNorm beta + 2*delta ∧
      ∀ t : Nat, actualOrdinalNorm xi ≤ t →
        actualOrdinalNorm beta ≤ (Phi^[delta]) t ∧
        actualHeadEndpoint xi t = actualHeadEndpoint beta ((Phi^[delta]) t) ∧
        actualHeadCount xi t = actualHeadCount beta ((Phi^[delta]) t)+delta ∧
        actualHeadValue xi t = actualHeadValue beta ((Phi^[delta]) t)+delta

end LogicLineages.OrdinalComparison.Targets
