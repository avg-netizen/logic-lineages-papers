module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteFrontProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteConsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalListCodecSupportProof InternalRecursionClosureLogicProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalClassContextAllPositionObserver
open OriginalAllPositionContextDeleteBaseProof OriginalAllPositionContextDeleteFrontProof
open OriginalAllPositionContextDeleteDropProof
open OriginalTypedDecoderTransportLogicalProof (iffRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem ready (gamma head tail cutoff deleted deletedTail frontValue suffix fullFront : InternalGraphComposition.OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hd : Nonempty (Derivation body Delta (consGraph deleted head deletedTail)))
    (hp : Nonempty (Derivation body Delta (graph2 front frontValue cutoff tail)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.drop suffix (suc cutoff) tail)))
    (hf : Nonempty (Derivation body Delta (consGraph fullFront head frontValue)))
    : Nonempty (Derivation body Delta
      ((graph2 deleteAt deleted (suc cutoff) gamma).iff
       (graph2 deleteAt deletedTail cutoff tail))) := by
  let P := graph2 deleteAt deleted (suc cutoff) gamma
  let Q := graph2 deleteAt deletedTail cutoff tail
  have hfront := frontCons gamma head tail cutoff frontValue fullFront hc hp hf
  have hdrop := dropConsBackward gamma head tail (suc cutoff) suffix hc hs
  have hforward : Nonempty (Derivation body (P :: Delta) Q) := by
    have ha := deleteAppendRecover (suc cutoff) gamma fullFront suffix deleted
      (withHyp hfront P) (withHyp hdrop P) ⟨Derivation.hypothesis List.mem_cons_self⟩
    have ht := OriginalContextInsertionSupportProof.appendTail fullFront head frontValue suffix
      deleted head deletedTail (withHyp hf P) (withHyp hd P) ha
    exact deleteValue cutoff tail frontValue suffix deletedTail (withHyp hp P) (withHyp hs P) ht
  have hbackward : Nonempty (Derivation body (Q :: Delta) P) := by
    have ha := deleteAppendRecover cutoff tail frontValue suffix deletedTail
      (withHyp hp Q) (withHyp hs Q) ⟨Derivation.hypothesis List.mem_cons_self⟩
    have ht := InternalApplicationValidityStackAppendListProof.consBackward
      fullFront head frontValue suffix deletedTail deleted (withHyp hf Q) ha (withHyp hd Q)
    exact deleteValue (suc cutoff) gamma fullFront suffix deleted (withHyp hfront Q) (withHyp hdrop Q) ht
  obtain ⟨hforward⟩ := hforward
  obtain ⟨hbackward⟩ := hbackward
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hforward)
    (Derivation.implicationIntroduction hbackward)⟩

theorem withSuffix (gamma head tail cutoff deleted deletedTail frontValue suffix : InternalGraphComposition.OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hd : Nonempty (Derivation body Delta (consGraph deleted head deletedTail)))
    (hp : Nonempty (Derivation body Delta (graph2 front frontValue cutoff tail)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.drop suffix (suc cutoff) tail)))
    : Nonempty (Derivation body Delta
      ((graph2 deleteAt deleted (suc cutoff) gamma).iff
       (graph2 deleteAt deletedTail cutoff tail))) := by
  apply programCases InternalListCodec.consCode (Fin.cons head (Fin.cons frontValue Fin.elim0)) _
  intro beta j Theta fullFront hj hnew
  simp only [iffRename,graph2Rename,sucRelabel]
  have hc' := renameInto hc j Theta hj
  simp only [consGraphRename,graph2Rename,sucRelabel] at hc'
  have hd' := renameInto hd j Theta hj
  simp only [consGraphRename,graph2Rename,sucRelabel] at hd'
  have hp' := renameInto hp j Theta hj
  simp only [consGraphRename,graph2Rename,sucRelabel] at hp'
  have hs' := renameInto hs j Theta hj
  simp only [consGraphRename,graph2Rename,sucRelabel] at hs'
  simp only [consTermRename,emptyRename,sucRelabel] at hnew
  exact ready (gamma.relabel j) (head.relabel j) (tail.relabel j) (cutoff.relabel j) (deleted.relabel j) (deletedTail.relabel j) (frontValue.relabel j) (suffix.relabel j) fullFront hc' hd' hp' hs' hnew

theorem withFront (gamma head tail cutoff deleted deletedTail frontValue : InternalGraphComposition.OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hd : Nonempty (Derivation body Delta (consGraph deleted head deletedTail)))
    (hp : Nonempty (Derivation body Delta (graph2 front frontValue cutoff tail)))
    : Nonempty (Derivation body Delta
      ((graph2 deleteAt deleted (suc cutoff) gamma).iff
       (graph2 deleteAt deletedTail cutoff tail))) := by
  apply programCases InternalRawListRecursion.drop (Fin.cons (suc cutoff) (Fin.cons tail Fin.elim0)) _
  intro beta j Theta suffix hj hnew
  simp only [iffRename,graph2Rename,sucRelabel]
  have hc' := renameInto hc j Theta hj
  simp only [consGraphRename,graph2Rename,sucRelabel] at hc'
  have hd' := renameInto hd j Theta hj
  simp only [consGraphRename,graph2Rename,sucRelabel] at hd'
  have hp' := renameInto hp j Theta hj
  simp only [consGraphRename,graph2Rename,sucRelabel] at hp'
  simp only [consTermRename,emptyRename,sucRelabel] at hnew
  exact withSuffix (gamma.relabel j) (head.relabel j) (tail.relabel j) (cutoff.relabel j) (deleted.relabel j) (deletedTail.relabel j) (frontValue.relabel j) suffix hc' hd' hp' hnew

theorem deleteConsIff (gamma head tail cutoff deleted deletedTail : InternalGraphComposition.OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hd : Nonempty (Derivation body Delta (consGraph deleted head deletedTail)))
    : Nonempty (Derivation body Delta
      ((graph2 deleteAt deleted (suc cutoff) gamma).iff
       (graph2 deleteAt deletedTail cutoff tail))) := by
  apply programCases front (Fin.cons cutoff (Fin.cons tail Fin.elim0)) _
  intro beta j Theta frontValue hj hnew
  simp only [iffRename,graph2Rename,sucRelabel]
  have hc' := renameInto hc j Theta hj
  simp only [consGraphRename,graph2Rename,sucRelabel] at hc'
  have hd' := renameInto hd j Theta hj
  simp only [consGraphRename,graph2Rename,sucRelabel] at hd'
  simp only [consTermRename,emptyRename,sucRelabel] at hnew
  exact withFront (gamma.relabel j) (head.relabel j) (tail.relabel j) (cutoff.relabel j) (deleted.relabel j) (deletedTail.relabel j) frontValue hc' hd' hnew

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteConsProof
