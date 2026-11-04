module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceEndpointDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceEndpointTargets
open Source PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.SourceEndpoint

/-- PENDING: paper06 lem:id1. This quantifies over ALL typed auxiliary terms
through the unchanged canonical-carrier graph, all source windows, arbitrary
simple types and binder contexts. The source has strict total ranked
precedence (paper.tex lines 77--82); the graph suppliers themselves accept
arbitrary Boolean tables and do not impose that termination premise. -/
def ActualSourceInternalAccessibility : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) → strictTotalPrecedence table →
  Nonempty (Derivation
    (sourceBody n arity Gamma (OrdinaryArithmeticQuotient.contextCode symbols S table)) []
    (allTermsFormula n arity Gamma (OrdinaryArithmeticQuotient.contextCode symbols S table)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceEndpointTargets
