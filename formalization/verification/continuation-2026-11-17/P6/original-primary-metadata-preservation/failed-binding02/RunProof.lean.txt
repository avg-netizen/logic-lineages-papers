module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.IterationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.SingletonProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.RunGraphProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.RunProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open SyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
attribute [local irreducible] OriginalConcreteStructuralEdge.edge OriginalConcreteHeadSignature.signature OriginalCandidates.candidates OriginalDecodedContextValidity.contextGuard SeededPrimaryPool.pool

open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z)
open InternalAcceptanceSupportProof

theorem preserved (n : Nat) (arity : Fin n → Nat)
    (count seed parameter pool out seedType seedRaw boundsRef rootTypeRef : OTerm alpha)
    (had : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (numeral 1) seed parameter)))
    (hpool : Nonempty (Derivation body Delta (graph2 (SeededPrimaryPool.pool (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity))) pool seed parameter)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing seed seedType seedRaw)))
    (hr : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.run (OriginalConcreteStructuralEdge.edge n arity)) out count pool seed parameter)))
    (hu : Nonempty (Derivation body Delta (accepted n arity seedType seedRaw rootTypeRef boundsRef))) :
    Nonempty (Derivation body Delta (allAccepted n arity out rootTypeRef boundsRef)) := by
  apply programCases InternalListCodec.consCode (Fin.cons seed (Fin.cons z Fin.elim0)) _
  intro beta j Theta singleton hj hsingle
  rw [allAcceptedRename]
  simp only [consTermRename,emptyRename,zRelabel] at hsingle
  have had' := renameInto had j Theta hj
  simp only [graph2Rename,graph3Rename,graph4Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename] at had'
  have hpool' := renameInto hpool j Theta hj
  simp only [graph2Rename,graph3Rename,graph4Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename] at hpool'
  have hs' := renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,graph4Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename] at hs'
  have hr' := renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,graph4Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename] at hr'
  have hu' := renameInto hu j Theta hj
  simp only [graph2Rename,graph3Rename,graph4Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename] at hu'
  have hi := RunGraphProof.recover (OriginalConcreteStructuralEdge.edge n arity)
    (count.relabel j) (pool.relabel j) (seed.relabel j) (parameter.relabel j)
    (out.relabel j) singleton hsingle hr'
  have hU := SingletonProof.accepted n arity singleton (seed.relabel j)
    (seedType.relabel j) (seedRaw.relabel j) (rootTypeRef.relabel j) (boundsRef.relabel j) hsingle hs' hu'
  exact IterationProof.preserved n arity (count.relabel j) (seed.relabel j) (parameter.relabel j)
    (pool.relabel j) singleton (out.relabel j) (boundsRef.relabel j) (rootTypeRef.relabel j)
    had' hpool' hi hU

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.RunProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.RunProof
