module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseRemoveBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseKeepBranchesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseInvariantProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseConsAtProof
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
open InternalApplicationStepPeelSupportProof (andLeft)
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)

theorem zeroBit (weight : Program 1) (list head tail needle acc rest actual bit remaining total tailSum restSum headWeight needleWeight actualWeight : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 Erase.state acc tail needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc z rest)))
    (hts : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) tailSum tail)))
    (hrs : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) restSum rest)))
    (hhw : Nonempty (Derivation body Delta (graph1 weight headWeight head)))
    (hnw : Nonempty (Derivation body Delta (graph1 weight needleWeight needle)))
    (hlt : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) total list)))
    (ih : Nonempty (Derivation body Delta (effect z tailSum restSum needleWeight)))
    (ha : Nonempty (Derivation body Delta (graph2 Erase.state actual list needle)))
    (hap : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing actual bit remaining)))
    (haw : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) actualWeight remaining))) :
    Nonempty (Derivation body Delta (effect bit total actualWeight needleWeight)) := by
  apply formulaCases (eqn head needle)
  · exact WeightedEraseRemoveBranchProof.remove weight list head tail needle acc rest actual bit remaining total tailSum restSum needleWeight actualWeight
      (withHyp hc _) (withHyp ht _) (withHyp hp _) ⟨Derivation.hypothesis List.mem_cons_self⟩
      (withHyp hts _) (withHyp hrs _) (withHyp hnw _) (withHyp hlt _) (withHyp ih _)
      (withHyp ha _) (withHyp hap _) (withHyp haw _)
  · exact WeightedEraseKeepBranchesProof.absent weight list head tail needle acc rest actual bit remaining total tailSum restSum headWeight needleWeight actualWeight
      (withHyp hc _) (withHyp ht _) (withHyp hp _) ⟨Derivation.hypothesis List.mem_cons_self⟩
      (withHyp hts _) (withHyp hrs _) (withHyp hhw _) (withHyp hlt _) (withHyp ih _)
      (withHyp ha _) (withHyp hap _) (withHyp haw _)

theorem atTail (weight : Program 1) (list head tail needle acc childBit rest actual bit remaining total tailSum restSum headWeight needleWeight actualWeight : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 Erase.state acc tail needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc childBit rest)))
    (hts : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) tailSum tail)))
    (hrs : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) restSum rest)))
    (hhw : Nonempty (Derivation body Delta (graph1 weight headWeight head)))
    (hnw : Nonempty (Derivation body Delta (graph1 weight needleWeight needle)))
    (hlt : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) total list)))
    (ih : Nonempty (Derivation body Delta (effect childBit tailSum restSum needleWeight)))
    (ha : Nonempty (Derivation body Delta (graph2 Erase.state actual list needle)))
    (hap : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing actual bit remaining)))
    (haw : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) actualWeight remaining))) :
    Nonempty (Derivation body Delta (effect bit total actualWeight needleWeight)) := by
  have hb := andLeft (EraseInvariantProof.actualResult tail needle acc childBit rest ht hp)
  apply OriginalTypedDecoderInternalBranchProof.orCases hb
  · have he : Nonempty (Derivation body ((eqn childBit z) :: Delta) (eqn childBit z)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hp' := headTransport InternalPairing.pairing acc childBit z (Fin.cons rest Fin.elim0) he (withHyp hp _)
    have ih' := WeightedEraseTransportProof.bitTransport childBit tailSum restSum needleWeight z he (withHyp ih _)
    exact zeroBit weight list head tail needle acc rest actual bit remaining total tailSum restSum headWeight needleWeight actualWeight
      (withHyp hc _) (withHyp ht _) hp' (withHyp hts _) (withHyp hrs _) (withHyp hhw _) (withHyp hnw _) (withHyp hlt _) ih'
      (withHyp ha _) (withHyp hap _) (withHyp haw _)
  · have he : Nonempty (Derivation body ((eqn childBit (suc z)) :: Delta) (eqn childBit (suc z))) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hp' := headTransport InternalPairing.pairing acc childBit (suc z) (Fin.cons rest Fin.elim0) he (withHyp hp _)
    have ih' := WeightedEraseTransportProof.bitTransport childBit tailSum restSum needleWeight (suc z) he (withHyp ih _)
    exact WeightedEraseKeepBranchesProof.found weight list head tail needle acc rest actual bit remaining total tailSum restSum headWeight needleWeight actualWeight
      (withHyp hc _) (withHyp ht _) hp' (withHyp hts _) (withHyp hrs _) (withHyp hhw _) (withHyp hlt _) ih'
      (withHyp ha _) (withHyp hap _) (withHyp haw _)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseConsAtProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseConsAtProof
