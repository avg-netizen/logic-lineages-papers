module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportBinaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportLeafAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalListProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.AcceptanceConstructorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (symm refl)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalRawSyntaxTransport
open OriginalUniverseDecoderTransport
open OriginalTypedDecoderTransportLogicalProof
open OriginalTypedDecoderInternalListProof (consArrowFields consNonzero)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem nilAccept (H : Program 1) (M W : Program 2) (raw gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph nilConstructor raw Fin.elim0))) :
    Nonempty (Derivation body Delta (Accepted H M W true z raw gamma context)) :=
  iffBackward (OriginalUniverseDecoderTransportLeafAcceptanceProof.nilIff H M W raw z gamma context hc)
    (andIntro (equalReflexive z) (equalReflexive z))

theorem consForward (H : Program 1) (M W : Program 2)
    (raw domain head tail types tailTypes gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw domain head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode types z tailTypes)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context))) :
    Nonempty (Derivation body Delta (eqn domain z ⊓
      (Accepted H M W false domain head gamma context ⊓
       Accepted H M W true tailTypes tail gamma context))) := by
  have h := iffForward (OriginalUniverseDecoderTransportBinaryAcceptanceProof.consIff H M W
    raw domain head tail types z tailTypes gamma context hc (consArrowFields types z tailTypes ht)) ha
  obtain ⟨he⟩ := andLeft (andRight h)
  rw [InternalControlGraphSupportProof.equalEqn] at he
  exact andIntro ⟨symm he⟩ (andRight (andRight h))

theorem consBackward (H : Program 1) (M W : Program 2)
    (raw domain head tail types tailTypes gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw domain head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode types z tailTypes)))
    (he : Nonempty (Derivation body Delta (eqn domain z)))
    (hh : Nonempty (Derivation body Delta (Accepted H M W false domain head gamma context)))
    (hr : Nonempty (Derivation body Delta (Accepted H M W true tailTypes tail gamma context))) :
    Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context)) := by
  obtain ⟨he⟩ := he
  have he' : Nonempty (Derivation body Delta (equal z domain)) := by
    rw [InternalControlGraphSupportProof.equalEqn]
    exact ⟨symm he⟩
  exact iffBackward (OriginalUniverseDecoderTransportBinaryAcceptanceProof.consIff H M W
    raw domain head tail types z tailTypes gamma context hc (consArrowFields types z tailTypes ht))
    (andIntro (consNonzero types z tailTypes ht) (andIntro he' (andIntro hh hr)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.AcceptanceConstructorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.AcceptanceConstructorProof
