module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedAgreementBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseSearchCompletenessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseInvariantProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseEffectProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.FoldRecoverProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedAgreementConsAtProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open WeightedAgreement WeightedAgreementBindingProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationStepPeelSupportProof (andIntro andRight)
open Continuation20261115.OriginalArgumentPermutationClosure.CountAgreement

theorem cons (weight : Program 1) (left head tail right acc bit rest ls rs tailSum restSum headWeight : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode left head tail)))
    (ha : Nonempty (Derivation body Delta (agreement left right)))
    (hv : Nonempty (Derivation body Delta (graph2 Erase.state acc right head)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit rest)))
    (hl : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) ls left)))
    (hr : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) rs right)))
    (ht : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) tailSum tail)))
    (hw : Nonempty (Derivation body Delta (graph1 weight headWeight head)))
    (hs : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) restSum rest)))
    (ih : Nonempty (Derivation body Delta (BelowRaw weight left))) :
    Nonempty (Derivation body Delta (eqn ls rs)) := by
  have hbit := EraseSearchCompletenessProof.found left head tail right acc bit rest hc ha hv hp
  have hcount := EraseInvariantProof.actualResult right head acc bit rest hv hp
  have hcount1 := EraseResultTransportProof.bitTransport right head bit (suc z) rest hbit hcount
  have htail := EraseCountCancellationProof.cancel left head tail right rest hc ha (andRight hcount1)
  have hsmall := InternalListCodecDecompositionSupportProof.consTailDescent left head tail hc
  have he := belowRawApply weight left tail rest tailSum restSum ih hsmall
    (andIntro htail (andIntro ht hs))
  have hwf := WeightedEraseInvariantProof.actualResult weight right head acc bit rest rs restSum headWeight hv hp hr hs hw
  have hwf1 := WeightedEraseTransportProof.bitTransport bit rs restSum headWeight (suc z) hbit hwf
  have hright := WeightedEraseEffectProof.foundValue rs restSum headWeight hwf1
  have hleft := FoldRecoverProof.cons weight left head tail tailSum headWeight ls hc ht hw hl
  have hleft' := OriginalCodeBoundsConstructors.ZeroMaximumProof.secondTransport merge ls headWeight tailSum restSum he hleft
  exact valueUnique merge ls rs ![headWeight,restSum] hleft' hright
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedAgreementConsAtProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedAgreementConsAtProof
