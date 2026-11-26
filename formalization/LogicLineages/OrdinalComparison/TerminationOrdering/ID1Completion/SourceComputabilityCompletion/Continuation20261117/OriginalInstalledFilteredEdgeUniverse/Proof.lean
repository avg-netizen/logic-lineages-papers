module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledFilteredEdgeUniverse.WindowQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledFilteredEdgeUniverse.Proof
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
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open OriginalUniverseDecoderTransportSyntaxProof (acceptedRename)
theorem atSource (n : Nat) (arity : Fin n → Nat)
 (seed parameter pool source target sourceType sourceRaw targetType targetRaw context gamma : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing source sourceType sourceRaw)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing target targetType targetRaw)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)))
 (had : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (numeral 1) seed parameter)))
 (hpool : Nonempty (Derivation body Delta (graph2 (SeededPrimaryPool.pool (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity))) pool seed parameter)))
 (hm : Nonempty (Derivation body Delta (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) pool target)))
 (he : Nonempty (Derivation body Delta (graph3 (OriginalConcreteStructuralEdge.edge n arity) (numeral 1) source target parameter)))
 (hu : Nonempty (Derivation body Delta (OriginalUniverseDecoderTransport.Accepted (OriginalConcreteHeadSignature.signature n arity) (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity) false sourceType sourceRaw gamma context)))
 :
 Nonempty (Derivation body Delta (OriginalUniverseDecoderTransport.Accepted (OriginalConcreteHeadSignature.signature n arity) (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity) false targetType targetRaw gamma context)) := by
 apply OriginalDecodedRank.SupportProof.pairCases context _
 intro beta j Theta window table hj hnew
 rw [acceptedRename]
 have hs' := renameInto hs j Theta hj
 simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hs'
 have ht' := renameInto ht j Theta hj
 simp only [graph2Rename,numeral,sucRelabel,zRelabel] at ht'
 have hp' := renameInto hp j Theta hj
 simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hp'
 have had' := renameInto had j Theta hj
 simp only [graph2Rename,numeral,sucRelabel,zRelabel] at had'
 have hpool' := renameInto hpool j Theta hj
 simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hpool'
 have hm' := renameInto hm j Theta hj
 simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hm'
 have he' := renameInto he j Theta hj
 simp only [graph3Rename,numeral,sucRelabel,zRelabel] at he'
 have hu' := renameInto hu j Theta hj
 simp only [acceptedRename,numeral,sucRelabel,zRelabel] at hu'
 exact WindowQueryProof.preserved n arity
  (seed.relabel j) (parameter.relabel j) (pool.relabel j) (source.relabel j) (target.relabel j) (sourceType.relabel j) (sourceRaw.relabel j) (targetType.relabel j) (targetRaw.relabel j) (context.relabel j) (gamma.relabel j) window table
  hs' ht' hp' had' hpool' hm' he' hu' hnew

theorem installedFilteredEdgeUniverse : Targets.InternalInstalledFilteredEdgeUniverse := by
 intro n arity body alpha Delta seed parameter pool source target sourceType sourceRaw targetType targetRaw context gamma
 exact atSource n arity seed parameter pool source target sourceType sourceRaw targetType targetRaw context gamma

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledFilteredEdgeUniverse.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledFilteredEdgeUniverse.Proof
