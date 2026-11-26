module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledEdgeReversal.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.ClosureSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledEdgeReversal.AtFieldsProof
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
 (source target parameter context gamma types sourceType sourceRaw targetType targetRaw window table symbols node reverseNode : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)))
 (hq : Nonempty (Derivation body Delta (graph1 OriginalUniverseDomainCoverage.contextTypes types context)))
 (ha : Nonempty (Derivation body Delta (WindowSourceHeadInclusion.ArrowClosed types)))
 (he : Nonempty (Derivation body Delta (graph3 (OriginalConcreteStructuralEdge.edge n arity) (numeral 1) source target parameter)))
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing source sourceType sourceRaw)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing target targetType targetRaw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing context window table)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing window symbols types)))
 (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node sourceRaw targetRaw)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing reverseNode targetRaw sourceRaw)))
: Nonempty (Derivation body Delta (graph3 (OriginalConcreteStructuralEdge.edge n arity) (numeral 1) target source parameter)) := by
 have hf := (OriginalConcreteStructuralEdge.Proof.internalEdge n arity body alpha Delta
   source target parameter sourceType sourceRaw targetType targetRaw context gamma hs ht hp).mp he
 have heq := andLeft hf
 have hguards := andLeft (andRight hf)
 have hctx := andLeft hguards
 have hsrc := andLeft (andRight hguards)
 have htgt := andRight (andRight hguards)
 have hcall := andRight (andRight hf)
 have hex := (OriginalConcreteStructuralEdge.SupportProof.atContextFactor n arity sourceRaw targetRaw context
   window table node (numeral 1) hc hn).mp hcall
 have hrev := OriginalRawExchangeSymmetry.Proof.symmetry n arity body alpha Delta
   sourceRaw targetRaw node reverseNode window symbols types hn hr hw hsrc htgt ha hex
 have hback := (OriginalConcreteStructuralEdge.SupportProof.atContextFactor n arity targetRaw sourceRaw context
   window table reverseNode (numeral 1) hc hr).mpr hrev
 obtain ⟨heq⟩ := heq
 exact (OriginalConcreteStructuralEdge.Proof.internalEdge n arity body alpha Delta
   target source parameter targetType targetRaw sourceType sourceRaw context gamma ht hs hp).mpr
   (andIntro ⟨InternalTagArithmeticSupportProof.symm heq⟩
     (andIntro (andIntro hctx (andIntro htgt hsrc)) hback))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledEdgeReversal.AtFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledEdgeReversal.AtFieldsProof
