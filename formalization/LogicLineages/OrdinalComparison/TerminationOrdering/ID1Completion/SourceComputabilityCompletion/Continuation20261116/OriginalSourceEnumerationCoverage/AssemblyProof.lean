module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceEnumerationCoverage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceEnumerationCoverage.DepthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceEnumerationCoverage.SelectorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceEnumerationCoverage.AssemblyProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalAdditionLawsProof (add)
open InternalOriginalOrderSyntaxProof (addRelabel)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atValues (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (seed param context gamma types heads typ raw pair size maxLabel seedSize seedLabel out count node metadata middle tail : OTerm alpha)
    (hcontext : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.context context seed param)))
    (hgamma : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.gamma gamma seed param)))
    (htypes : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.types types seed param)))
    (hheads : Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.heads n arity) heads seed param)))
    (hseedSize : Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.size n) seedSize seed param)))
    (hseedLabel : Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.labels n) seedLabel seed param)))
    (hclosed : Nonempty (Derivation body Delta (WindowSourceHeadInclusion.ArrowClosed types)))
    (ha : Nonempty (Derivation body Delta (OriginalUniverseDecoderInternalAcceptance.TermAccepted H
      (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity) typ raw gamma context)))
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size maxLabel)))
    (hs : Nonempty (Derivation body Delta (InternalLessThan.strictLess size (suc seedSize))))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess maxLabel (suc seedLabel))))
    (hout : Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.enumerated n arity) out seed param)))
    (hcount : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.bound count seed param)))
    (hnode : Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.node n) node seed param)))
    (hmetadata : Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.parameter n arity) metadata seed param)))
    (hmiddle : Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.InputProof.metadataMiddle n arity) middle seed param)))
    (htail : Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.InputProof.metadataTail n) tail seed param))) :
    Nonempty (Derivation body Delta (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) out raw)) := by
  have hlength := SelectorsProof.lengthRecover seed param gamma count hgamma hcount
  have hfuel := SelectorsProof.fuelValue n seed param seedSize hseedSize
  have hnodePair := OriginalClassCodes.InputProof.nodeRecover n seed param node count (add seedSize seedSize) hnode hcount hfuel
  have htailPair := OriginalClassCodes.InputProof.tailRecover n seed param tail seedLabel seedSize htail hseedLabel hseedSize
  have hmiddlePair := OriginalClassCodes.InputProof.middleRecover n arity seed param middle heads tail hmiddle hheads htail
  have hmetadataPair := OriginalClassCodes.InputProof.parameterRecover n arity seed param metadata types middle hmetadata htypes hmiddle
  have henumeration := OriginalClassCodes.InputProof.enumerationRecover n arity seed param node metadata out hout hnode hmetadata
  have hfields := OriginalUniverseFieldsCoverage.Proof.internalTermFields n arity H body alpha Delta
    seed param context types heads typ raw gamma count pair size maxLabel seedLabel seedSize
    hcontext htypes hheads hclosed ha hlength hb hp hs hl
  have hdepth := DepthProof.sourceDepth n H (OriginalUniverseDomainCoverage.member n)
    (OriginalGuardedHeadSourceCoverage.window n arity) typ raw gamma context pair size maxLabel seedSize ha hb hp hs
  exact (OriginalEnumerationMembership.Proof.internalMembership n body alpha Delta
    node metadata middle tail out raw count (add seedSize seedSize) types heads seedLabel seedSize
    hnodePair hmetadataPair hmiddlePair htailPair henumeration).mpr (andIntro hfields hdepth)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceEnumerationCoverage.AssemblyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceEnumerationCoverage.AssemblyProof
