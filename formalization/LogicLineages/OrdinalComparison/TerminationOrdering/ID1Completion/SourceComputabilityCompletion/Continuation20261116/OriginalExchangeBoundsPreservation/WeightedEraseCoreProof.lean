module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseConsAtProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseChildBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseNilProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open WeightedErase WeightedEraseSyntaxProof WeightedEraseBindingProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z eqn eqnRelabel zRelabel)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open OriginalTypedDecoderTransportLogicalProof (notRename)

theorem nonzero (weight : Program 1) (raw needle acc bit rest total remainingWeight needleWeight : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 Erase.state acc raw needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit rest)))
    (ht : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) total raw)))
    (hr : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) remainingWeight rest)))
    (hw : Nonempty (Derivation body Delta (graph1 weight needleWeight needle)))
    (ih : Nonempty (Derivation body Delta (BelowRaw weight raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not))
    : Nonempty (Derivation body Delta (effect bit total remainingWeight needleWeight)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (WeightedEraseChildQueriesProof.queries weight) ![raw,needle] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![raw,needle] i).relabel j) = ![raw.relabel j,needle.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  rw [effectRename]
  have hvj := renameInto hv j Theta hj
  have hpj := renameInto hp j Theta hj
  have htj := renameInto ht j Theta hj
  have hrj := renameInto hr j Theta hj
  have hwj := renameInto hw j Theta hj
  have ihj := renameInto ih j Theta hj
  have hnj := renameInto hn j Theta hj
  rw [graph2Rename] at hvj hpj
  rw [graph1Rename] at htj hrj hwj
  rw [belowRawRename] at ihj
  simp only [notRename,eqnRelabel,zRelabel] at hnj
  obtain ⟨hc,hchild,hpair⟩ := WeightedEraseChildBaseProof.recover weight (raw.relabel j) (needle.relabel j) ys hnj hq
  obtain ⟨hts,hrs,hhw⟩ := WeightedEraseChildQueriesProof.recover weight (raw.relabel j) (needle.relabel j) ys hq
  have hsmall := InternalListCodecDecompositionSupportProof.consTailDescent (raw.relabel j) (ys 0) (ys 1) hc
  have htail := belowRawApply weight (raw.relabel j) (ys 1) (needle.relabel j) (ys 2) (ys 3) (ys 4)
    (ys 5) (ys 6) (needleWeight.relabel j) ihj hsmall
    (andIntro (andIntro hchild hpair) (andIntro hts (andIntro hrs hwj)))
  exact WeightedEraseConsAtProof.atTail weight (raw.relabel j) (ys 0) (ys 1) (needle.relabel j)
    (ys 2) (ys 3) (ys 4) (acc.relabel j) (bit.relabel j) (rest.relabel j)
    (total.relabel j) (ys 5) (ys 6) (ys 7) (needleWeight.relabel j) (remainingWeight.relabel j)
    hc hchild hpair hts hrs hhw hwj htj htail hvj hpj hrj

theorem atRaw (weight : Program 1) (raw needle acc bit rest total remainingWeight needleWeight : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 Erase.state acc raw needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit rest)))
    (ht : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) total raw)))
    (hr : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) remainingWeight rest)))
    (hw : Nonempty (Derivation body Delta (graph1 weight needleWeight needle)))
    (ih : Nonempty (Derivation body Delta (BelowRaw weight raw)))
    : Nonempty (Derivation body Delta (effect bit total remainingWeight needleWeight)) := by
  apply formulaCases (eqn raw z)
  · have he : Nonempty (Derivation body ((eqn raw z) :: Delta) (eqn raw z)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hv0 := headTransport Erase.state acc raw z (Fin.cons needle Fin.elim0) he (withHyp hv _)
    have ht0 := headTransport (Fold.weighted weight) total raw z Fin.elim0 he (withHyp ht _)
    exact WeightedEraseNilProof.nil weight needle acc bit rest total remainingWeight needleWeight
      hv0 (withHyp hp _) ht0 (withHyp hr _)
  · exact nonzero weight raw needle acc bit rest total remainingWeight needleWeight
      (withHyp hv _) (withHyp hp _) (withHyp ht _) (withHyp hr _) (withHyp hw _) (withHyp ih _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedEraseCoreProof
