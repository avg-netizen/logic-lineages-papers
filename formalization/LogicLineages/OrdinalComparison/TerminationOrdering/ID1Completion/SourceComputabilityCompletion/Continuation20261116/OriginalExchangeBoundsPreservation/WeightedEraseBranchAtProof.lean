module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseEffectProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseKeepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseBranchAtProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open WeightedErase
open InternalTagArithmeticSyntaxProof (z suc eqn)

theorem remove (weight : Program 1) (list head tail needle acc rest out total tailSum restSum needleWeight : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 Erase.state acc tail needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc z rest)))
    (he : Nonempty (Derivation body Delta (eqn head needle)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (suc z) rest)))
    (hts : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) tailSum tail)))
    (hnw : Nonempty (Derivation body Delta (graph1 weight needleWeight needle)))
    (hlt : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) total list)))
    (ih : Nonempty (Derivation body Delta (effect z tailSum restSum needleWeight))) :
    Nonempty (Derivation body Delta (graph2 Erase.state out list needle)) ∧
    Nonempty (Derivation body Delta (effect (suc z) total restSum needleWeight)) := by
  constructor
  · exact EraseKeepProof.cons list head tail needle acc out hc ht
      (EraseValueProof.removeValue head acc needle rest out hp ho he)
  · exact WeightedEraseEffectProof.found total restSum needleWeight
      (WeightedEraseValueProof.remove weight list head tail needle rest total tailSum restSum needleWeight
        hc hts hnw hlt he (WeightedEraseEffectProof.absentValue tailSum restSum needleWeight ih))

theorem absent (weight : Program 1) (list head tail needle acc rest kept out total tailSum restSum headWeight remainingSum needleWeight : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 Erase.state acc tail needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc z rest)))
    (he : Nonempty (Derivation body Delta (eqn head needle).not))
    (hk : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode kept head rest)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out z kept)))
    (hts : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) tailSum tail)))
    (hrs : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) restSum rest)))
    (hhw : Nonempty (Derivation body Delta (graph1 weight headWeight head)))
    (hlt : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) total list)))
    (hkt : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) remainingSum kept)))
    (ih : Nonempty (Derivation body Delta (effect z tailSum restSum needleWeight))) :
    Nonempty (Derivation body Delta (graph2 Erase.state out list needle)) ∧
    Nonempty (Derivation body Delta (effect z total remainingSum needleWeight)) := by
  constructor
  · exact EraseKeepProof.cons list head tail needle acc out hc ht
      (EraseKeepProof.absent head acc needle rest kept out hp hk ho he)
  · exact WeightedEraseEffectProof.absent total remainingSum needleWeight
      (WeightedEraseValueProof.keepAbsent weight list head tail kept rest total tailSum restSum headWeight remainingSum
        hc hk hts hrs hhw hlt hkt (WeightedEraseEffectProof.absentValue tailSum restSum needleWeight ih))

theorem found (weight : Program 1) (list head tail needle acc rest kept out total tailSum restSum headWeight remainingSum needleWeight : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 Erase.state acc tail needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc (suc z) rest)))
    (hk : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode kept head rest)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (suc z) kept)))
    (hts : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) tailSum tail)))
    (hrs : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) restSum rest)))
    (hhw : Nonempty (Derivation body Delta (graph1 weight headWeight head)))
    (hlt : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) total list)))
    (hkt : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) remainingSum kept)))
    (ih : Nonempty (Derivation body Delta (effect (suc z) tailSum restSum needleWeight))) :
    Nonempty (Derivation body Delta (graph2 Erase.state out list needle)) ∧
    Nonempty (Derivation body Delta (effect (suc z) total remainingSum needleWeight)) := by
  constructor
  · exact EraseKeepProof.cons list head tail needle acc out hc ht
      (EraseKeepProof.alreadyFound head acc needle rest kept out hp hk ho)
  · exact WeightedEraseEffectProof.found total remainingSum needleWeight
      (WeightedEraseValueProof.keepFound weight list head tail kept rest total tailSum restSum headWeight needleWeight remainingSum
        hc hk hts hrs hhw hlt hkt (WeightedEraseEffectProof.foundValue tailSum restSum needleWeight ih))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseBranchAtProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseBranchAtProof
