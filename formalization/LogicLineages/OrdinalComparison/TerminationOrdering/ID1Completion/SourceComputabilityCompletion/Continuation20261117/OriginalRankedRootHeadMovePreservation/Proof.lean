module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.CallerSignatureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.HeadIdentityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel eqnRelabel)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalRawSyntaxTransport OriginalUniverseDecoderTransport
open OriginalUniverseDecoderTransportSyntaxProof (acceptedRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
open Continuation20261116.OriginalConcreteHeadSignature

attribute [local irreducible] programGraph

theorem ordinary : Targets.InternalOrdinaryRankedHeadMove := by
  intro n arity M W body alpha Delta left right f g base target typ gamma context symbols windowTypes hlc hrc htag hlg hrg hmove ha
  have hleft := RootGuardProof.ordinary n left f base hlc hlg
  have hright := RootGuardProof.ordinary n right g target hrc hrg
  have hm := (OriginalHeadMove.InternalProof.internalAcceptance n arity body alpha Delta
    f base g target symbols windowTypes).mp hmove
  have he := HeadIdentityProof.rankedEqual f g htag (andRight (andLeft hm))
  have hbg := andRight hleft
  have htg := andRight hright
  have hp := andRight hm
  exact CallerSignatureProof.ordinary n arity M W left right f g base target typ gamma context
    hlc hrc he hbg htg hp htag (andLeft hleft) ha

theorem numbered : Targets.InternalNumberedRankedHeadMove := by
  intro n arity M W body alpha Delta left right label f g recorded base target extraTypes extras typ gamma context symbols windowTypes hlc hrc htag hlg hrg hmove ha
  have hleft := RootGuardProof.numbered n left label f recorded base extraTypes extras hlc hlg
  have hright := RootGuardProof.numbered n right label g recorded target extraTypes extras hrc hrg
  have hm := (OriginalHeadMove.InternalProof.internalAcceptance n arity body alpha Delta
    f base g target symbols windowTypes).mp hmove
  have he := HeadIdentityProof.rankedEqual f g htag (andRight (andLeft hm))
  have hbg := andRight hleft
  have htg := andRight hright
  have hp := andRight hm
  exact CallerSignatureProof.numbered n arity M W left right label f g recorded base target extraTypes extras typ gamma context
    hlc hrc he hbg htg hp htag (andLeft hleft) ha

theorem rankedRootHeadMoves : Targets.InternalRankedRootHeadMoves := ⟨ordinary,numbered⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.Proof
