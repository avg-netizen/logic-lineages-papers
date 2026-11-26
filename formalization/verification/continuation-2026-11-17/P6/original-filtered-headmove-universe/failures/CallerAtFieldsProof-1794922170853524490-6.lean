module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.PermutationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportUnaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportBinaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportUnaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportBinaryAcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.CallerAtFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalRawSyntaxTransport OriginalUniverseDecoderTransport
open OriginalTypedDecoderStepSpecification (StepArrowFields)
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem ordinary (n : Nat) (H : Program 1) (M W : Program 2)
    (left right f g base target typ gamma context sourceData sourceResult sourceTypes targetData targetResult targetTypes : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor left f base)))
    (hrc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor right g target)))
    (hbg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) base)))
    (htg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) target)))
    (hperm : Nonempty (Derivation body Delta (graph2 OriginalArgumentPermutation.check (suc z) base target)))
    (hs : Nonempty (Derivation body Delta (graph1 H sourceData f)))
    (ht : Nonempty (Derivation body Delta (graph1 H targetData g)))
    (hsf : Nonempty (Derivation body Delta (StepArrowFields sourceData sourceResult sourceTypes)))
    (htf : Nonempty (Derivation body Delta (StepArrowFields targetData targetResult targetTypes)))
    (hw : Nonempty (Derivation body Delta (graph2 W (suc z) g context)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W false typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (OriginalTypedDecoderTransport.Accepted H false typ right gamma))) :
    Nonempty (Derivation body Delta (Accepted H M W false typ right gamma context)) := by
  have h := iffForward (OriginalUniverseDecoderTransportUnaryAcceptanceProof.ordinaryIff H M W
    left f base sourceData sourceResult sourceTypes typ gamma context hlc hs hsf) ha
  have p := iffForward (OriginalTypedDecoderTransportUnaryAcceptanceProof.ordinaryIff H
    right g target targetData targetResult targetTypes typ gamma hrc ht htf) hp
  have ha' := PermutationProof.preserved n H M W sourceTypes targetTypes base target gamma context
    hbg htg (andRight (andRight (andRight (andRight h)))) (andRight (andRight p)) hperm
  exact iffBackward (OriginalUniverseDecoderTransportUnaryAcceptanceProof.ordinaryIff H M W
    right g target targetData targetResult targetTypes typ gamma context hrc ht htf)
    (andIntro (andLeft h) (andIntro hw (andIntro (andLeft p)
      (andIntro (andLeft (andRight p)) ha'))))

theorem numbered (n : Nat) (H : Program 1) (M W : Program 2)
    (left right label recorded extraTypes extras f g base target typ gamma context sourceData sourceResult sourceTypes targetData targetResult targetTypes : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (programGraph numberedConstructor left ![label,f,recorded,base,extraTypes,extras])))
    (hrc : Nonempty (Derivation body Delta (programGraph numberedConstructor right ![label,g,recorded,target,extraTypes,extras])))
    (hbg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) base)))
    (htg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) target)))
    (hperm : Nonempty (Derivation body Delta (graph2 OriginalArgumentPermutation.check (suc z) base target)))
    (hs : Nonempty (Derivation body Delta (graph1 H sourceData f)))
    (ht : Nonempty (Derivation body Delta (graph1 H targetData g)))
    (hsf : Nonempty (Derivation body Delta (StepArrowFields sourceData sourceResult sourceTypes)))
    (htf : Nonempty (Derivation body Delta (StepArrowFields targetData targetResult targetTypes)))
    (hw : Nonempty (Derivation body Delta (graph2 W (suc z) g context)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W false typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (OriginalTypedDecoderTransport.Accepted H false typ right gamma))) :
    Nonempty (Derivation body Delta (Accepted H M W false typ right gamma context)) := by
  have h := iffForward (OriginalUniverseDecoderTransportBinaryAcceptanceProof.numberedIff H M W
    left label f recorded base extraTypes extras sourceData sourceResult sourceTypes typ gamma context hlc hs hsf) ha
  have p := iffForward (OriginalTypedDecoderTransportBinaryAcceptanceProof.numberedIff H
    right label g recorded target extraTypes extras targetData targetResult targetTypes typ gamma hrc ht htf) hp
  have ha' := PermutationProof.preserved n H M W sourceTypes targetTypes base target gamma context
    hbg htg (andLeft (andRight (andRight (andRight (andRight h))))) (andLeft (andRight (andRight p))) hperm
  exact iffBackward (OriginalUniverseDecoderTransportBinaryAcceptanceProof.numberedIff H M W
    right label g recorded target extraTypes extras targetData targetResult targetTypes typ gamma context hrc ht htf)
    (andIntro (andLeft h) (andIntro hw (andIntro (andLeft p)
      (andIntro (andLeft (andRight p)) (andIntro ha' (andRight (andRight (andRight (andRight (andRight h))))))))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.CallerAtFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.CallerAtFieldsProof
