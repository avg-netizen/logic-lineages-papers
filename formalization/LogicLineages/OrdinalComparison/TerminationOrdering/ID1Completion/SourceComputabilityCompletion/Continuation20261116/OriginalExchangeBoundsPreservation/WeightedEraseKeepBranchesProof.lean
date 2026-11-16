module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseBranchAtProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseConstructQueriesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseKeepBranchesProof
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
open OriginalTypedDecoderTransportLogicalProof (notRename)

theorem absent (weight : Program 1) (list head tail needle acc rest actual actualBit remaining total tailSum restSum headWeight needleWeight actualWeight : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 Erase.state acc tail needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc z rest)))
    (he : Nonempty (Derivation body Delta (eqn head needle).not))
    (hts : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) tailSum tail)))
    (hrs : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) restSum rest)))
    (hhw : Nonempty (Derivation body Delta (graph1 weight headWeight head)))
    (hlt : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) total list)))
    (ih : Nonempty (Derivation body Delta (effect z tailSum restSum needleWeight)))
    (ha : Nonempty (Derivation body Delta (graph2 Erase.state actual list needle)))
    (hap : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing actual actualBit remaining)))
    (haw : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) actualWeight remaining))) :
    Nonempty (Derivation body Delta (effect actualBit total actualWeight needleWeight)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (WeightedEraseConstructQueriesProof.queries weight) ![z,head,rest] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![z,head,rest] i).relabel j) = ![z,head.relabel j,rest.relabel j] := by
    funext i
    fin_cases i
    · change (z : OTerm alpha).relabel j = z
      simp only [sucRelabel,zRelabel]
    · rfl
    · rfl
  rw [hx] at hq
  rw [effectRename]
  obtain ⟨hk,ho,hks⟩ := WeightedEraseConstructQueriesProof.recover weight z (head.relabel j) (rest.relabel j) ys hq
  have hcj := renameInto hc j Theta hj
  have htj := renameInto ht j Theta hj
  have hpj := renameInto hp j Theta hj
  have hej := renameInto he j Theta hj
  have htsj := renameInto hts j Theta hj
  have hrsj := renameInto hrs j Theta hj
  have hhwj := renameInto hhw j Theta hj
  have hltj := renameInto hlt j Theta hj
  have ihj := renameInto ih j Theta hj
  have haj := renameInto ha j Theta hj
  have hapj := renameInto hap j Theta hj
  have hawj := renameInto haw j Theta hj
  simp only [graph2Rename,zRelabel,sucRelabel] at hcj htj hpj haj hapj
  simp only [notRename,eqnRelabel] at hej
  rw [graph1Rename] at htsj hrsj hhwj hltj hawj
  simp only [effectRename,zRelabel,sucRelabel] at ihj
  obtain ⟨hv,hef⟩ := WeightedEraseBranchAtProof.absent weight (list.relabel j) (head.relabel j)
    (tail.relabel j) (needle.relabel j) (acc.relabel j) (rest.relabel j) (ys 0) (ys 1)
    (total.relabel j) (tailSum.relabel j) (restSum.relabel j) (headWeight.relabel j) (ys 2) (needleWeight.relabel j)
    hcj htj hpj hej hk ho htsj hrsj hhwj hltj hks ihj
  exact WeightedEraseOutputProof.transfer weight (list.relabel j) (needle.relabel j) (ys 1) z
    (ys 0) (actual.relabel j) (actualBit.relabel j) (remaining.relabel j) (total.relabel j)
    (ys 2) (actualWeight.relabel j) (needleWeight.relabel j)
    hv ho haj hapj hks hawj hef

theorem found (weight : Program 1) (list head tail needle acc rest actual actualBit remaining total tailSum restSum headWeight needleWeight actualWeight : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 Erase.state acc tail needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc (suc z) rest)))
    (hts : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) tailSum tail)))
    (hrs : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) restSum rest)))
    (hhw : Nonempty (Derivation body Delta (graph1 weight headWeight head)))
    (hlt : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) total list)))
    (ih : Nonempty (Derivation body Delta (effect (suc z) tailSum restSum needleWeight)))
    (ha : Nonempty (Derivation body Delta (graph2 Erase.state actual list needle)))
    (hap : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing actual actualBit remaining)))
    (haw : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) actualWeight remaining))) :
    Nonempty (Derivation body Delta (effect actualBit total actualWeight needleWeight)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (WeightedEraseConstructQueriesProof.queries weight) ![(suc z),head,rest] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![(suc z),head,rest] i).relabel j) = ![(suc z),head.relabel j,rest.relabel j] := by
    funext i
    fin_cases i
    · change ((suc z) : OTerm alpha).relabel j = (suc z)
      simp only [sucRelabel,zRelabel]
    · rfl
    · rfl
  rw [hx] at hq
  rw [effectRename]
  obtain ⟨hk,ho,hks⟩ := WeightedEraseConstructQueriesProof.recover weight (suc z) (head.relabel j) (rest.relabel j) ys hq
  have hcj := renameInto hc j Theta hj
  have htj := renameInto ht j Theta hj
  have hpj := renameInto hp j Theta hj
  have htsj := renameInto hts j Theta hj
  have hrsj := renameInto hrs j Theta hj
  have hhwj := renameInto hhw j Theta hj
  have hltj := renameInto hlt j Theta hj
  have ihj := renameInto ih j Theta hj
  have haj := renameInto ha j Theta hj
  have hapj := renameInto hap j Theta hj
  have hawj := renameInto haw j Theta hj
  simp only [graph2Rename,zRelabel,sucRelabel] at hcj htj hpj haj hapj
  rw [graph1Rename] at htsj hrsj hhwj hltj hawj
  simp only [effectRename,zRelabel,sucRelabel] at ihj
  obtain ⟨hv,hef⟩ := WeightedEraseBranchAtProof.found weight (list.relabel j) (head.relabel j)
    (tail.relabel j) (needle.relabel j) (acc.relabel j) (rest.relabel j) (ys 0) (ys 1)
    (total.relabel j) (tailSum.relabel j) (restSum.relabel j) (headWeight.relabel j) (ys 2) (needleWeight.relabel j)
    hcj htj hpj hk ho htsj hrsj hhwj hltj hks ihj
  exact WeightedEraseOutputProof.transfer weight (list.relabel j) (needle.relabel j) (ys 1) (suc z)
    (ys 0) (actual.relabel j) (actualBit.relabel j) (remaining.relabel j) (total.relabel j)
    (ys 2) (actualWeight.relabel j) (needleWeight.relabel j)
    hv ho haj hapj hks hawj hef
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseKeepBranchesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseKeepBranchesProof
