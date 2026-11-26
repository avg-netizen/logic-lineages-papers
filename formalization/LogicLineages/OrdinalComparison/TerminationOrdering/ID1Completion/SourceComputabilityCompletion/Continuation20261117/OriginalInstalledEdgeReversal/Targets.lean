module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseDomainCoverage.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledEdgeReversal.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114 Continuation20261115 Continuation20261116
/-- Exact installed E reversal at the same actual parameter. Only its observed context
and selected types with ArrowClosed are explicit; both Code guards, context validity
and packed root-type equality are derived from forward E. Raw pairs are queried. -/
def InternalReversal : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (source target parameter context gamma types : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)) →
  Nonempty (Derivation body Delta (graph1 OriginalUniverseDomainCoverage.contextTypes types context)) →
  Nonempty (Derivation body Delta (WindowSourceHeadInclusion.ArrowClosed types)) →
  Nonempty (Derivation body Delta
    (graph3 (OriginalConcreteStructuralEdge.edge n arity) (numeral 1) source target parameter)) →
  Nonempty (Derivation body Delta
    (graph3 (OriginalConcreteStructuralEdge.edge n arity) (numeral 1) target source parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledEdgeReversal.Targets
