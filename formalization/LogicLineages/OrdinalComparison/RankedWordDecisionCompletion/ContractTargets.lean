module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.ContractDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.ContractTargets
open PolynomialGraphCompletion

/-- Entire printed paper08 lem:row: one actual total effective compiler for
arbitrary finite admitted source row collections, preserving their raw names
and literal domains. This existential is a construction obligation; no solver
or cancellation theorem is assumed as an input. -/
def FullRankedCancellation : Prop :=
  ∃ compiler : Nat → Nat → List Row → Package,
    Computable (fun input : Nat × Nat × List Row =>
      encodePackage (compiler input.1 input.2.1 input.2.2)) ∧
    ∀ D maximum rows, 3 ≤ D → (∀ r ∈ rows, RowAllowed D r) →
      PackageCorrect D maximum rows (compiler D maximum rows)

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.ContractTargets
