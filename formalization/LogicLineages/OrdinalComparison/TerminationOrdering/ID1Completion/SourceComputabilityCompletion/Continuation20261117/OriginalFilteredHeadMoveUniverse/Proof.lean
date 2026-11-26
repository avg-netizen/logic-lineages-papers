module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.CallerQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.WindowProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.PlainTargetProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.RootGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
attribute [local irreducible] programGraph

theorem ordinary : Targets.InternalOrdinary := by
  intro n arity B body alpha Delta seed parameter out candidate typ gamma context symbols types left right f g base target
    hlc hrc hsp htp hc hg hs htypes hcontext hlg hrg hmove ha hout hmem
  let H := OriginalConcreteHeadSignature.signature n arity
  let M := OriginalUniverseDomainCoverage.member n
  let W := OriginalGuardedHeadSourceCoverage.window n arity
  have hleft := OriginalRankedRootHeadMovePreservation.RootGuardProof.ordinary n left f base hlc hlg
  have hright := OriginalRankedRootHeadMovePreservation.RootGuardProof.ordinary n right g target hrc hrg
  have hm := (OriginalHeadMove.InternalProof.internalAcceptance n arity body alpha Delta
    f base g target symbols types).mp hmove
  have hselectors := WindowProof.selectors seed parameter context symbols types hc hs htypes
  have hw := WindowProof.rebuild n arity g context symbols types hcontext (andLeft hright)
    (andLeft hselectors) (andRight hselectors) (andRight (andLeft (andLeft hm)))
  have hp := PlainTargetProof.filtered n arity B seed parameter out candidate typ left right gamma context
    hsp htp hc hg hcontext ha hout hmem
  exact CallerQueryProof.ordinaryComplete n H M W left right f g base target typ gamma context
    hlc hrc (andRight hleft) (andRight hright) (andRight hm) hw ha hp

theorem numbered : Targets.InternalNumbered := by
  intro n arity B body alpha Delta seed parameter out candidate typ gamma context symbols types left right label f g recorded base target extraTypes extras
    hlc hrc hsp htp hc hg hs htypes hcontext hlg hrg hmove ha hout hmem
  let H := OriginalConcreteHeadSignature.signature n arity
  let M := OriginalUniverseDomainCoverage.member n
  let W := OriginalGuardedHeadSourceCoverage.window n arity
  have hleft := OriginalRankedRootHeadMovePreservation.RootGuardProof.numbered n left label f recorded base extraTypes extras hlc hlg
  have hright := OriginalRankedRootHeadMovePreservation.RootGuardProof.numbered n right label g recorded target extraTypes extras hrc hrg
  have hm := (OriginalHeadMove.InternalProof.internalAcceptance n arity body alpha Delta
    f base g target symbols types).mp hmove
  have hselectors := WindowProof.selectors seed parameter context symbols types hc hs htypes
  have hw := WindowProof.rebuild n arity g context symbols types hcontext (andLeft hright)
    (andLeft hselectors) (andRight hselectors) (andRight (andLeft (andLeft hm)))
  have hp := PlainTargetProof.filtered n arity B seed parameter out candidate typ left right gamma context
    hsp htp hc hg hcontext ha hout hmem
  exact CallerQueryProof.numberedComplete n H M W left right label recorded extraTypes extras f g base target typ gamma context
    hlc hrc (andRight hleft) (andRight hright) (andRight hm) hw ha hp

theorem filteredHeadMoveUniverse : Targets.InternalFilteredHeadMoveUniverse := ⟨ordinary,numbered⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.Proof
