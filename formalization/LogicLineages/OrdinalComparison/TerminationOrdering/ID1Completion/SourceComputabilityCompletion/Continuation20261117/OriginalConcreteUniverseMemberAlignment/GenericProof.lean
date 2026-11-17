module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteUniverseMemberAlignment.InclusionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteUniverseMemberAlignment.GenericProof
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

theorem acceptedIff (H : Program 1) (M W : Program 2) (arguments : Bool)
    (typ raw gamma context : OTerm alpha) :
    Nonempty (Derivation body Delta
      ((Accepted H (InternalOriginalUniformContextMembership.contextMember (OriginalContextMemberLift.liftMember M)) W arguments typ raw gamma context).iff
        (Accepted H M W arguments typ raw gamma context))) := by
  let ML := InternalOriginalUniformContextMembership.contextMember (OriginalContextMemberLift.liftMember M)
  let A := Accepted H ML W arguments typ raw gamma context
  let B := Accepted H M W arguments typ raw gamma context
  obtain ⟨hf⟩ := OriginalUniverseMemberTransport.Proof.transport H ML M W arguments typ raw gamma context
    (InclusionProof.forward M context (Delta := A :: Delta))
    (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := OriginalUniverseMemberTransport.Proof.transport H M ML W arguments typ raw gamma context
    (InclusionProof.backward M context (Delta := B :: Delta))
    (show Nonempty (Derivation body (B :: Delta) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem both (H : Program 1) (M W : Program 2) (typ raw gamma context : OTerm alpha) :
    let ML := InternalOriginalUniformContextMembership.contextMember (OriginalContextMemberLift.liftMember M)
    Nonempty (Derivation body Delta
      (((TermAccepted H ML W typ raw gamma context).iff (TermAccepted H M W typ raw gamma context)) ⊓
       ((ArgumentsAccepted H ML W typ raw gamma context).iff (ArgumentsAccepted H M W typ raw gamma context)))) :=
  andIntro (acceptedIff H M W false typ raw gamma context) (acceptedIff H M W true typ raw gamma context)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteUniverseMemberAlignment.GenericProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteUniverseMemberAlignment.GenericProof
