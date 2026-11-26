module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseBranchAtProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseOutputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseRemoveBranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open WeightedErase WeightedEraseSyntaxProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel eqnRelabel)

theorem remove (weight : Program 1) (list head tail needle acc rest actual bit remaining total tailSum restSum needleWeight actualWeight : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 Erase.state acc tail needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc z rest)))
    (he : Nonempty (Derivation body Delta (eqn head needle)))
    (hts : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) tailSum tail)))
    (hrs : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) restSum rest)))
    (hnw : Nonempty (Derivation body Delta (graph1 weight needleWeight needle)))
    (hlt : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) total list)))
    (ih : Nonempty (Derivation body Delta (effect z tailSum restSum needleWeight)))
    (ha : Nonempty (Derivation body Delta (graph2 Erase.state actual list needle)))
    (hap : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing actual bit remaining)))
    (haw : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) actualWeight remaining))) :
    Nonempty (Derivation body Delta (effect bit total actualWeight needleWeight)) := by
  apply InternalAcceptanceSupportProof.programCases InternalPairing.pairing ![suc z,rest] _
  intro beta j Theta out hj ho
  have hx : (fun i => (![suc z,rest] i).relabel j) = ![suc z,rest.relabel j] := by
    funext i
    fin_cases i
    · change (suc (z : OTerm alpha)).relabel j = suc z
      simp only [sucRelabel,zRelabel]
    · rfl
  rw [hx] at ho
  rw [effectRename]
  have hcj := renameInto hc j Theta hj
  have htj := renameInto ht j Theta hj
  have hpj := renameInto hp j Theta hj
  have hej := renameInto he j Theta hj
  have htsj := renameInto hts j Theta hj
  have hrsj := renameInto hrs j Theta hj
  have hnwj := renameInto hnw j Theta hj
  have hltj := renameInto hlt j Theta hj
  have ihj := renameInto ih j Theta hj
  have haj := renameInto ha j Theta hj
  have hapj := renameInto hap j Theta hj
  have hawj := renameInto haw j Theta hj
  simp only [graph2Rename,zRelabel] at hcj htj hpj haj hapj
  rw [eqnRelabel] at hej
  rw [graph1Rename] at htsj hrsj hnwj hltj hawj
  simp only [effectRename,zRelabel] at ihj
  obtain ⟨hv,hef⟩ := WeightedEraseBranchAtProof.remove weight (list.relabel j) (head.relabel j)
    (tail.relabel j) (needle.relabel j) (acc.relabel j) (rest.relabel j) out (total.relabel j)
    (tailSum.relabel j) (restSum.relabel j) (needleWeight.relabel j)
    hcj htj hpj hej ho htsj hnwj hltj ihj
  exact WeightedEraseOutputProof.transfer weight (list.relabel j) (needle.relabel j) out (suc z)
    (rest.relabel j) (actual.relabel j) (bit.relabel j) (remaining.relabel j) (total.relabel j)
    (restSum.relabel j) (actualWeight.relabel j) (needleWeight.relabel j)
    hv ho haj hapj hrsj hawj hef
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseRemoveBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseRemoveBranchProof
