module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawSameContextTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalContextInsertion
/-- Literal raw expansion preserves the original window coordinate. No source or
admissibility predicate is assumed; the child context may change. -/
def ActualCases : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (raw parameter window gamma jobs count index child : OTerm alpha) (psi : Formula alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)) →
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs raw parameter)) →
 Nonempty (Derivation body Delta (lengthGraph count jobs)) →
 Nonempty (Derivation body Delta (Below index count)) →
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup child index jobs)) →
 (∀ (beta : Type) (rho : alpha → beta) (Theta : List (Formula beta))
   (childRaw childParameter childGamma : OTerm beta),
   (∀ f ∈ Delta, f.relabel rho ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (child.relabel rho) childRaw childParameter)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing childParameter (window.relabel rho) childGamma)) →
   Nonempty (Derivation body Theta (psi.relabel rho))) →
 Nonempty (Derivation body Delta psi)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawSameContextTargets
