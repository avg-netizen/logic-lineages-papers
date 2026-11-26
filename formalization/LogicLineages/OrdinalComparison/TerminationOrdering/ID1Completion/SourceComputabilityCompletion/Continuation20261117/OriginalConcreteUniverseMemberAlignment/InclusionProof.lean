module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalContextMemberLift.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteUniverseMemberAlignment.InclusionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalUniverseMemberTransport.Definitions
open OriginalUniverseDecoderInternalAcceptance
open OriginalUniverseDecoderTransport (Accepted)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem forward (M : Program 2) (context : OTerm alpha) :
    Nonempty (Derivation body Delta (MemberIncluded
      (InternalOriginalUniformContextMembership.contextMember (OriginalContextMemberLift.liftMember M)) M context)) := by
  have h := OriginalContextMemberLift.Proof.contextMemberLift M body (alpha ⊕ Fin 1)
    (Delta.map (fun q => q.relabel Sum.inl)) (numeral 1) (.var (.inr 0)) (context.relabel Sum.inl)
  obtain ⟨d⟩ := andLeft h
  exact ⟨Derivation.universalIntroduction d⟩

theorem backward (M : Program 2) (context : OTerm alpha) :
    Nonempty (Derivation body Delta (MemberIncluded M
      (InternalOriginalUniformContextMembership.contextMember (OriginalContextMemberLift.liftMember M)) context)) := by
  have h := OriginalContextMemberLift.Proof.contextMemberLift M body (alpha ⊕ Fin 1)
    (Delta.map (fun q => q.relabel Sum.inl)) (numeral 1) (.var (.inr 0)) (context.relabel Sum.inl)
  obtain ⟨d⟩ := andRight h
  exact ⟨Derivation.universalIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteUniverseMemberAlignment.InclusionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteUniverseMemberAlignment.InclusionProof
