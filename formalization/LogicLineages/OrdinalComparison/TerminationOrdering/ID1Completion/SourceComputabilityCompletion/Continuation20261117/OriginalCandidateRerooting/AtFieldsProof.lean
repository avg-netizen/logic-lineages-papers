module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.RequestRenameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.PipelineStableProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryTypedCarrierV2.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.AtFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalTagArithmeticSupportProof (symm)

theorem reroot (n : Nat) (arity : Fin n → Nat)
    (seed parameter out candidate seedQ targetQ seedType seedRaw targetType targetRaw seedBounds targetBounds : OTerm alpha)
    (q : Request n arity body Delta seed parameter out candidate seedQ targetQ)
    (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing seed seedType seedRaw)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate targetType targetRaw)))
    (hsb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) seedBounds seedRaw)))
    (htb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) targetBounds targetRaw))) :
    Nonempty (Derivation body Delta (eqn seedQ targetQ)) := by
  have hm := OriginalPrimaryMetadataPreservation.Proof.primaryMetadataPreservation n arity body alpha Delta
    seed parameter out candidate seedType seedRaw targetType targetRaw seedBounds targetBounds
    hs ht hsb htb q.admitted q.primary q.member
  obtain ⟨htype⟩ := andLeft hm
  obtain ⟨hbound⟩ := andRight hm
  have ht' := headTransport InternalPairing.pairing candidate targetType seedType
    (Fin.cons targetRaw Fin.elim0) ⟨symm htype⟩ ht
  have htb' := outputTransport (OriginalCodeBoundsRecursion.bounds n) targetBounds seedBounds
    ![targetRaw] ⟨symm hbound⟩ htb
  have had := OriginalPrimaryTypedCarrierV2.Proof.primaryTypedCarrier n arity
    (OriginalConcreteStructuralEdge.structural n arity) body alpha Delta seed parameter out candidate
    q.admitted q.primary q.member
  let data : DataDefinitions.Data n arity body Delta seed candidate parameter :=
    { root := seedType, left := seedRaw, right := targetRaw, bounds := seedBounds,
      sourcePair := hs, targetPair := ht', sourceBounds := hsb, targetBounds := htb',
      sourceAdmitted := q.admitted, targetAdmitted := had }
  have hc := PipelineStableProof.candidates n arity body alpha Delta seed candidate parameter seedQ
    data q.sourceCandidates
  exact valueUnique (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity)) seedQ targetQ ![candidate,parameter] hc q.targetCandidates

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.AtFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.AtFieldsProof
