module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.SignatureCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.PreservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportUnaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportBinaryAcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.CallerAtSignatureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalRawSyntaxTransport OriginalUniverseDecoderTransport
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
open Continuation20261116.OriginalConcreteHeadSignature
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem ordinary (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right f g base target typ gamma context count args packed : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor left f base)))
    (hrc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor right g target)))
    (he : Nonempty (Derivation body Delta (eqn f g)))
    (hbg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) base)))
    (htg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) target)))
    (hp : Nonempty (Derivation body Delta (graph2 OriginalArgumentPermutation.check (suc z) base target)))
    (hargs : Nonempty (Derivation body Delta (graph1 groundList args count)))
    (hH : Nonempty (Derivation body Delta (graph1 (signature n arity) (suc packed) f)))
    (hfields : Nonempty (Derivation body Delta (OriginalTypedDecoderStepSpecification.StepArrowFields (suc packed) z args)))
    (ha : Nonempty (Derivation body Delta (Accepted (signature n arity) M W false typ left gamma context))) :
    Nonempty (Derivation body Delta (Accepted (signature n arity) M W false typ right gamma context)) := by
  have h := iffForward (OriginalUniverseDecoderTransportUnaryAcceptanceProof.ordinaryIff (signature n arity) M W
    left f base (suc packed) z args typ gamma context hlc hH hfields) ha
  have hb := andRight (andRight (andRight (andRight h)))
  have ht := Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.PreservationProof.preserved
    n arity M W body alpha Delta count args base target gamma context hbg htg hargs hb hp
  have hW := headTransport W (suc z) f g ![context] he (andLeft (andRight h))
  have hG := headTransport (signature n arity) (suc packed) f g Fin.elim0 he hH
  exact iffBackward (OriginalUniverseDecoderTransportUnaryAcceptanceProof.ordinaryIff (signature n arity) M W
    right g target (suc packed) z args typ gamma context hrc hG hfields)
    (andIntro (andLeft h) (andIntro hW (andIntro (andLeft (andRight (andRight h)))
      (andIntro (andLeft (andRight (andRight (andRight h)))) ht))))

theorem numbered (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right label f g recorded base target extraTypes extras typ gamma context count args packed : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (programGraph numberedConstructor left ![label,f,recorded,base,extraTypes,extras])))
    (hrc : Nonempty (Derivation body Delta (programGraph numberedConstructor right ![label,g,recorded,target,extraTypes,extras])))
    (he : Nonempty (Derivation body Delta (eqn f g)))
    (hbg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) base)))
    (htg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) target)))
    (hp : Nonempty (Derivation body Delta (graph2 OriginalArgumentPermutation.check (suc z) base target)))
    (hargs : Nonempty (Derivation body Delta (graph1 groundList args count)))
    (hH : Nonempty (Derivation body Delta (graph1 (signature n arity) (suc packed) f)))
    (hfields : Nonempty (Derivation body Delta (OriginalTypedDecoderStepSpecification.StepArrowFields (suc packed) z args)))
    (ha : Nonempty (Derivation body Delta (Accepted (signature n arity) M W false typ left gamma context))) :
    Nonempty (Derivation body Delta (Accepted (signature n arity) M W false typ right gamma context)) := by
  have h := iffForward (OriginalUniverseDecoderTransportBinaryAcceptanceProof.numberedIff (signature n arity) M W
    left label f recorded base extraTypes extras (suc packed) z args typ gamma context hlc hH hfields) ha
  have hb := andLeft (andRight (andRight (andRight (andRight h))))
  have ht := Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.PreservationProof.preserved
    n arity M W body alpha Delta count args base target gamma context hbg htg hargs hb hp
  have hW := headTransport W (suc z) f g ![context] he (andLeft (andRight h))
  have hG := headTransport (signature n arity) (suc packed) f g Fin.elim0 he hH
  exact iffBackward (OriginalUniverseDecoderTransportBinaryAcceptanceProof.numberedIff (signature n arity) M W
    right label g recorded target extraTypes extras (suc packed) z args typ gamma context hrc hG hfields)
    (andIntro (andLeft h) (andIntro hW (andIntro (andLeft (andRight (andRight h)))
      (andIntro (andLeft (andRight (andRight (andRight h))))
        (andIntro ht (andRight (andRight (andRight (andRight (andRight h))))))))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.CallerAtSignatureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.CallerAtSignatureProof
