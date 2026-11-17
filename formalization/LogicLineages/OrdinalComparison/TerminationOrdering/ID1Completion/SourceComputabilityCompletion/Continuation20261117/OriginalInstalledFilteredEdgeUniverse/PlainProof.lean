module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledFilteredEdgeUniverse.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryTypedCarrierV2.PoolProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.PlainTargetProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledFilteredEdgeUniverse.PlainProof
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

theorem filtered (n : Nat) (arity : Fin n → Nat)
 (seed parameter pool target typ raw context gamma : OTerm alpha)
 (htp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing target typ raw)))
 (hpp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)))
 (ha : Nonempty (Derivation body Delta
   (graph2 (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity)
     (OriginalDecodedContextValidity.contextGuard n)) (numeral 1) seed parameter)))
 (hp : Nonempty (Derivation body Delta
   (graph2 (SeededPrimaryPool.pool
     (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n))
     (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity))) pool seed parameter)))
 (hm : Nonempty (Derivation body Delta
   (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) pool target))) :
 Nonempty (Derivation body Delta
   (OriginalTypedDecoderTransport.Accepted (OriginalConcreteHeadSignature.signature n arity) false typ raw gamma)) := by
 have ht := OriginalPrimaryTypedCarrierV2.PoolProof.accepted n arity
   (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)
   seed parameter pool target ha hp hm
 have hg : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.gamma gamma seed parameter)) :=
   unaryValue InternalUnpair.right (.projection 1) gamma parameter ![seed,parameter]
     (pairRight parameter context gamma hpp) (projectionValue 1 ![seed,parameter])
 exact OriginalFilteredHeadMoveUniverse.PlainTargetProof.unpack
   (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)
   seed target parameter typ raw gamma htp hg ht

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledFilteredEdgeUniverse.PlainProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledFilteredEdgeUniverse.PlainProof
