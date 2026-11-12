module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildPacketDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobReconcileProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobPacketReconcileProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeel (graph5)
open InternalControlGraphSupportProof (headTransport)
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof (symm)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalInternalJobAdmissible OriginalInternalJobChildPacket
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem reconcilePacket (H : Program 1) (M W : Program 2)
 (index canonical role typ raw rawCell parameter gamma c child childRole childType typed stored annotation
  expectedRole expectedType expectedRaw expectedGamma expectedParameter expectedAnnotation
  childRaw childParameter childGamma : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (eqn index canonical)))
 (hpacket : Nonempty (Derivation body Delta (Packet H M W canonical role typ raw rawCell parameter c gamma
   expectedRole expectedType expectedRaw expectedGamma expectedParameter expectedAnnotation)))
 (hd : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.decorate child index role typ raw rawCell)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child childRole typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed childType stored)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing annotation childRole childType)))
 (hcr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing stored childRaw childParameter)))
 (hcg : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter c childGamma))) :
 Nonempty (Derivation body Delta (Admissible H M W childRole childType childRaw childGamma c)) := by
 have he := andLeft (andRight (andRight hpacket))
 have hv := andLeft (andRight (andRight (andRight hpacket)))
 have haccept := andRight (andRight (andRight (andRight hpacket)))
 obtain ⟨hi⟩ := hi
 have hv' := headTransport OriginalHereditaryAnnotatedExpansion.annotation expectedAnnotation canonical index
   (Fin.cons role (Fin.cons typ (Fin.cons raw Fin.elim0))) (Nonempty.intro (symm hi)) hv
 exact OriginalInternalJobReconcileProof.reconcile H M W index role typ raw rawCell child childRole childType typed stored annotation
   expectedAnnotation expectedRole expectedType expectedRaw expectedParameter expectedGamma childRaw childParameter childGamma c
   hd hp ht ha he hv' (andLeft hpacket) (andLeft (andRight hpacket)) hcr hcg haccept
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobPacketReconcileProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobPacketReconcileProof
