module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.EdgeSourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.WitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.EdgeWitnessProof
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

theorem fromWitness (n : Nat) (arity : Fin n → Nat)
    (seed parameter pool reached candidate targetType targetRaw context gamma : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)))
    (had : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (numeral 1) seed parameter)))
    (hpool : Nonempty (Derivation body Delta (graph2 (SeededPrimaryPool.pool (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity))) pool seed parameter)))
    (hu : Nonempty (Derivation body Delta (allAccepted n arity reached gamma context)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate targetType targetRaw)))
    (hm : Nonempty (Derivation body Delta (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) pool candidate)))
    (hw : Nonempty (Derivation body Delta (PrimaryExpansionSoundness.sourceWitness (OriginalConcreteStructuralEdge.edge n arity) reached candidate parameter))) :
    Nonempty (Derivation body Delta (accepted n arity targetType targetRaw gamma context)) := by
  apply PrimaryExpansionSoundness.WitnessProof.casesWitness (OriginalConcreteStructuralEdge.edge n arity) reached candidate parameter _ hw
  intro beta j Theta source hj hsource hedge
  rw [acceptedRename]
  have hp' := renameInto hp j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename,PrimaryExpansionSoundness.WitnessProof.witnessRename] at hp'
  have had' := renameInto had j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename,PrimaryExpansionSoundness.WitnessProof.witnessRename] at had'
  have hpool' := renameInto hpool j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename,PrimaryExpansionSoundness.WitnessProof.witnessRename] at hpool'
  have hu' := renameInto hu j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename,PrimaryExpansionSoundness.WitnessProof.witnessRename] at hu'
  have ht' := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename,PrimaryExpansionSoundness.WitnessProof.witnessRename] at ht'
  have hm' := renameInto hm j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename,PrimaryExpansionSoundness.WitnessProof.witnessRename] at hm'
  exact EdgeSourceProof.fromSource n arity (seed.relabel j) (parameter.relabel j)
    (pool.relabel j) (reached.relabel j) source (candidate.relabel j)
    (targetType.relabel j) (targetRaw.relabel j) (context.relabel j) (gamma.relabel j)
    hp' had' hpool' hu' ht' hm' hsource hedge

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.EdgeWitnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.EdgeWitnessProof
