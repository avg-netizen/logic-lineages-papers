module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.CallerQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.WindowProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.RootGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.HeadLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc z)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open Continuation20261114 Continuation20261115 Continuation20261116
open OriginalRawSyntaxTransport Induction
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem ordinary (n : Nat) (arity : Fin n → Nat)
    (left right f g base target typ gamma context symbols types window : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor left f base)))
    (hrc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor right g target)))
    (hlg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) left)))
    (hrg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) right)))
    (henv : Nonempty (Derivation body Delta (environment n context symbols types window)))
    (hmove : Nonempty (Derivation body Delta
      (programGraph (OriginalHeadMove.headMove n arity) (suc z) ![f,base,g,target,symbols,types])))
    (ha : Nonempty (Derivation body Delta (accepted n arity false typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (plain n arity false typ right gamma))) :
    Nonempty (Derivation body Delta (accepted n arity false typ right gamma context)) := by
  have hleft := OriginalRankedRootHeadMovePreservation.RootGuardProof.ordinary n left f base hlc hlg
  have hright := OriginalRankedRootHeadMovePreservation.RootGuardProof.ordinary n right g target hrc hrg
  have hm := (OriginalHeadMove.InternalProof.internalAcceptance n arity body alpha Delta
    f base g target symbols types).mp hmove
  have hw := OriginalFilteredHeadMoveUniverse.WindowProof.rebuild n arity g context symbols types
    (andLeft henv) (andLeft hright) (andLeft (andRight henv))
    (andLeft (andRight (andRight henv))) (andRight (andLeft (andLeft hm)))
  exact OriginalFilteredHeadMoveUniverse.CallerQueryProof.ordinaryComplete n
    (OriginalConcreteHeadSignature.signature n arity) (OriginalUniverseDomainCoverage.member n)
    (OriginalGuardedHeadSourceCoverage.window n arity) left right f g base target typ gamma context
    hlc hrc (andRight hleft) (andRight hright) (andRight hm) hw ha hp

theorem numbered (n : Nat) (arity : Fin n → Nat)
    (left right label recorded extraTypes extras f g base target typ gamma context symbols types window : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (programGraph numberedConstructor left ![label,f,recorded,base,extraTypes,extras])))
    (hrc : Nonempty (Derivation body Delta (programGraph numberedConstructor right ![label,g,recorded,target,extraTypes,extras])))
    (hlg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) left)))
    (hrg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) right)))
    (henv : Nonempty (Derivation body Delta (environment n context symbols types window)))
    (hmove : Nonempty (Derivation body Delta
      (programGraph (OriginalHeadMove.headMove n arity) (suc z) ![f,base,g,target,symbols,types])))
    (ha : Nonempty (Derivation body Delta (accepted n arity false typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (plain n arity false typ right gamma))) :
    Nonempty (Derivation body Delta (accepted n arity false typ right gamma context)) := by
  have hleft := OriginalRankedRootHeadMovePreservation.RootGuardProof.numbered n left label f recorded base extraTypes extras hlc hlg
  have hright := OriginalRankedRootHeadMovePreservation.RootGuardProof.numbered n right label g recorded target extraTypes extras hrc hrg
  have hm := (OriginalHeadMove.InternalProof.internalAcceptance n arity body alpha Delta
    f base g target symbols types).mp hmove
  have hw := OriginalFilteredHeadMoveUniverse.WindowProof.rebuild n arity g context symbols types
    (andLeft henv) (andLeft hright) (andLeft (andRight henv))
    (andLeft (andRight (andRight henv))) (andRight (andLeft (andLeft hm)))
  exact OriginalFilteredHeadMoveUniverse.CallerQueryProof.numberedComplete n
    (OriginalConcreteHeadSignature.signature n arity) (OriginalUniverseDomainCoverage.member n)
    (OriginalGuardedHeadSourceCoverage.window n arity) left right label recorded extraTypes extras f g base target typ gamma context
    hlc hrc (andRight hleft) (andRight hright) (andRight hm) hw ha hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.HeadLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.HeadLeafProof
