module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.EdgeWitnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.ExpansionProof
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
open InternalBetaTotalityProof InternalQuotientComparisonProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem preserved (n : Nat) (arity : Fin n → Nat)
    (seed parameter pool reached out boundsRef rootTypeRef : OTerm alpha)
    (had : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (numeral 1) seed parameter)))
    (hpool : Nonempty (Derivation body Delta (graph2 (SeededPrimaryPool.pool (OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)) (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity))) pool seed parameter)))
    (he : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.expand (OriginalConcreteStructuralEdge.edge n arity)) out pool reached parameter)))
    (hu : Nonempty (Derivation body Delta (allAccepted n arity reached rootTypeRef boundsRef))) :
    Nonempty (Derivation body Delta (allAccepted n arity out rootTypeRef boundsRef)) := by
  apply InvariantProof.introduce n arity out rootTypeRef boundsRef
  intro beta j Theta candidate targetType targetRaw hj hm ht
  have had' := renameInto had j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename] at had'
  have hpool' := renameInto hpool j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename] at hpool'
  have he' := renameInto he j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename] at he'
  have hu' := renameInto hu j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename,allAcceptedRename,acceptedRename] at hu'
  obtain ⟨hd⟩ := PrimaryExpansionSoundness.Proof.expansionSoundness (OriginalConcreteStructuralEdge.edge n arity)
    (pool.relabel j) (reached.relabel j) (parameter.relabel j) (out.relabel j) candidate he' hm
  let A := graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) (reached.relabel j) candidate
  let B := graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) (pool.relabel j) candidate ⊓
    PrimaryExpansionSoundness.sourceWitness (OriginalConcreteStructuralEdge.edge n arity) (reached.relabel j) candidate (parameter.relabel j)
  obtain ⟨ha⟩ := InvariantProof.eliminate n arity (reached.relabel j) candidate targetType targetRaw
    (rootTypeRef.relabel j) (boundsRef.relabel j) (withHyp hu' A)
    ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ht A)
  have hb : Nonempty (Derivation body (B :: Theta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb'⟩ := EdgeWitnessProof.fromWitness n arity (seed.relabel j) (parameter.relabel j)
    (pool.relabel j) (reached.relabel j) candidate targetType targetRaw
    (boundsRef.relabel j) (rootTypeRef.relabel j) (withHyp had' B)
    (withHyp hpool' B) (withHyp hu' B) (withHyp ht B) (andLeft hb) (andRight hb)
  exact ⟨disjunctionElimination hd (Derivation.implicationIntroduction ha)
    (Derivation.implicationIntroduction hb')⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.ExpansionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.ExpansionProof
