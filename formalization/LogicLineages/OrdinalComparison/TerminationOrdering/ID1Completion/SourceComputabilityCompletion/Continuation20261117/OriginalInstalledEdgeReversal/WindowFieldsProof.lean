module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledEdgeReversal.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.ClosureSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledEdgeReversal.NodeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledEdgeReversal.PairTransportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledEdgeReversal.WindowFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
open WindowSourceHeadInclusion.ClosureSyntaxProof (closureRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem reverse (n : Nat) (arity : Fin n → Nat)
 (source target parameter context gamma types sourceType sourceRaw targetType targetRaw window table symbols actualTypes : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)))
 (hq : Nonempty (Derivation body Delta (graph1 OriginalUniverseDomainCoverage.contextTypes types context)))
 (ha : Nonempty (Derivation body Delta (WindowSourceHeadInclusion.ArrowClosed types)))
 (he : Nonempty (Derivation body Delta (graph3 (OriginalConcreteStructuralEdge.edge n arity) (numeral 1) source target parameter)))
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing source sourceType sourceRaw)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing target targetType targetRaw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing context window table)))
 (hwa : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing window symbols actualTypes)))
: Nonempty (Derivation body Delta (graph3 (OriginalConcreteStructuralEdge.edge n arity) (numeral 1) target source parameter)) := by
 have hactual : Nonempty (Derivation body Delta (graph1 OriginalUniverseDomainCoverage.contextTypes actualTypes context)) :=
   unaryValue InternalUnpair.right InternalUnpair.left actualTypes window ![context]
     (pairRight window symbols actualTypes hwa) (pairLeft context window table hc)
 have heq := valueUnique OriginalUniverseDomainCoverage.contextTypes actualTypes types ![context] hactual hq
 have hw := PairTransportProof.rightInput window symbols actualTypes types heq hwa
 exact NodeProof.reverse n arity source target parameter context gamma types
   sourceType sourceRaw targetType targetRaw window table symbols hp hq ha he hs ht hc hw

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledEdgeReversal.WindowFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledEdgeReversal.WindowFieldsProof
