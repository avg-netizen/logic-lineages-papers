module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledFilteredEdgeUniverse.PlainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledFilteredEdgeUniverse.TypeTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledFilteredEdgeUniverse.AtFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem preserved (n : Nat) (arity : Fin n → Nat)
 (seed parameter pool source target sourceType sourceRaw targetType targetRaw context gamma window table symbols types node : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing source sourceType sourceRaw)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing target targetType targetRaw)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)))
 (had : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (numeral 1) seed parameter)))
 (hpool : Nonempty (Derivation body Delta (graph2 (SeededPrimaryPool.pool (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity))) pool seed parameter)))
 (hm : Nonempty (Derivation body Delta (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) pool target)))
 (he : Nonempty (Derivation body Delta (graph3 (OriginalConcreteStructuralEdge.edge n arity) (numeral 1) source target parameter)))
 (hu : Nonempty (Derivation body Delta (OriginalUniverseDecoderTransport.Accepted (OriginalConcreteHeadSignature.signature n arity) (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity) false sourceType sourceRaw gamma context)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing context window table)))
 (hw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing window symbols types)))
 (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node sourceRaw targetRaw)))
 :
 Nonempty (Derivation body Delta (OriginalUniverseDecoderTransport.Accepted (OriginalConcreteHeadSignature.signature n arity) (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity) false targetType targetRaw gamma context)) := by
 have hf := (OriginalConcreteStructuralEdge.Proof.internalEdge n arity body alpha Delta
   source target parameter sourceType sourceRaw targetType targetRaw context gamma hs ht hp).mp he
 have heq := InternalApplicationStepPeelSupportProof.andLeft hf
 have hguards := InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight hf)
 have hctx := InternalApplicationStepPeelSupportProof.andLeft hguards
 have hsrc := InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight hguards)
 have htgt := InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hguards)
 have hcall := InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hf)
 have hex := (OriginalConcreteStructuralEdge.SupportProof.atContextFactor n arity sourceRaw targetRaw context
   window table node (numeral 1) hc hn).mp hcall
 have hsym : Nonempty (Derivation body Delta (graph1 OriginalGuardedHeadSourceCoverage.contextSymbols symbols context)) :=
   unaryValue InternalUnpair.left InternalUnpair.left symbols window ![context]
     (pairLeft window symbols types hw) (pairLeft context window table hc)
 have htypes : Nonempty (Derivation body Delta (graph1 OriginalUniverseDomainCoverage.contextTypes types context)) :=
   unaryValue InternalUnpair.right InternalUnpair.left types window ![context]
     (pairRight window symbols types hw) (pairLeft context window table hc)
 have hplain := PlainProof.filtered n arity seed parameter pool target targetType targetRaw context gamma ht hp had hpool hm
 have hus := TypeTransportProof.transport (OriginalConcreteHeadSignature.signature n arity)
   (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
   sourceType targetType sourceRaw gamma context heq hu
 exact OriginalPlainAwareExchangeUniverse.Proof.term n arity body alpha Delta
   targetType sourceRaw targetRaw gamma context symbols types window node
   hctx hsym htypes hw hn hsrc htgt hex hus hplain

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledFilteredEdgeUniverse.AtFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledFilteredEdgeUniverse.AtFieldsProof
