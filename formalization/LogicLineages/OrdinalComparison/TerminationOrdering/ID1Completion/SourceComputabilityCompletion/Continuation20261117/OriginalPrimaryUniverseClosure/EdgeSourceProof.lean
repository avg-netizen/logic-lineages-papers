module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.InvariantProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalInstalledFilteredEdgeUniverse.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.EdgeSourceProof
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

theorem fromSource (n : Nat) (arity : Fin n → Nat)
    (seed parameter pool reached source candidate targetType targetRaw context gamma : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)))
    (had : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (numeral 1) seed parameter)))
    (hpool : Nonempty (Derivation body Delta (graph2 (SeededPrimaryPool.pool (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity))) pool seed parameter)))
    (hu : Nonempty (Derivation body Delta (allAccepted n arity reached gamma context)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate targetType targetRaw)))
    (hm : Nonempty (Derivation body Delta (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) pool candidate)))
    (hsource : Nonempty (Derivation body Delta (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) reached source)))
    (hedge : Nonempty (Derivation body Delta (graph3 (OriginalConcreteStructuralEdge.edge n arity) (numeral 1) source candidate parameter))) :
    Nonempty (Derivation body Delta (accepted n arity targetType targetRaw gamma context)) := by
  apply OriginalDecodedRank.SupportProof.pairCases source _
  intro beta j Theta sourceType sourceRaw hj hpair
  rw [acceptedRename]
  have hp' := renameInto hp j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename] at hp'
  have had' := renameInto had j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename] at had'
  have hpool' := renameInto hpool j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename] at hpool'
  have hu' := renameInto hu j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename] at hu'
  have ht' := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename] at ht'
  have hm' := renameInto hm j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename] at hm'
  have hsource' := renameInto hsource j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename] at hsource'
  have hedge' := renameInto hedge j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename] at hedge'
  have hs := InvariantProof.eliminate n arity (reached.relabel j) (source.relabel j)
    sourceType sourceRaw (gamma.relabel j) (context.relabel j) hu' hsource' hpair
  exact OriginalInstalledFilteredEdgeUniverse.Proof.atSource n arity
    (seed.relabel j) (parameter.relabel j) (pool.relabel j) (source.relabel j)
    (candidate.relabel j) sourceType sourceRaw (targetType.relabel j) (targetRaw.relabel j)
    (context.relabel j) (gamma.relabel j) hpair ht' hp' had' hpool' hm' hedge' hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.EdgeSourceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.EdgeSourceProof
