module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteLengthSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteDropProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSliceInductionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteLengthCoreProof
open InternalSliceInductionSyntaxProof (eqnRename)
open OriginalAllPositionContextDeleteInductionCoreProof (contextNonzero)
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding row rowInstantiate rowSuccessor
open InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof InternalSquareRootArithmeticSupportProof
open InternalListCodecSupportProof InternalSourceInversionSupportProof
open InternalBetaTotalityProof (addHyp)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open OriginalContextInsertionSupportProof
open OriginalAllPositionContextDeleteLengthSyntaxProof hiding rowInstantiate rowSuccessor
open OriginalClassContextAllPositionObserver (deleteAt)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}


open OriginalAllPositionContextDeleteInductionCoreProof (contextNonzero tailCases)

theorem zeroAtCons (count gamma head tail deleted d : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hf : Nonempty (Derivation body Delta (fields count gamma z deleted d))) :
    Nonempty (Derivation body Delta (eqn count (suc d))) := by
  have hd := andLeft (andRight (andRight hf))
  obtain ⟨he⟩ := valueUnique deleteAt deleted tail (Fin.cons z (Fin.cons gamma Fin.elim0)) hd
    (OriginalAllPositionContextDeleteBaseProof.deleteZero gamma head tail hc)
  have ht := headTransport length d deleted tail Fin.elim0 ⟨he⟩ (andRight (andRight (andRight hf)))
  exact lengthConsRecover gamma head tail count d hc (andLeft hf) ht

theorem successorValues (count gamma cutoff head tail deleted d tailCount deletedTail freshDeleted td : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row cutoff)))
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hf : Nonempty (Derivation body Delta (fields count gamma (suc cutoff) deleted d)))
    (hlen : Nonempty (Derivation body Delta (lengthGraph tailCount tail)))
    (hdel : Nonempty (Derivation body Delta (graph2 deleteAt deletedTail cutoff tail)))
    (hcons : Nonempty (Derivation body Delta (consGraph freshDeleted head deletedTail)))
    (htd : Nonempty (Derivation body Delta (lengthGraph td deletedTail))) :
    Nonempty (Derivation body Delta (eqn count (suc d))) := by
  obtain ⟨heCount⟩ := lengthConsRecover gamma head tail count tailCount hc (andLeft hf) hlen
  obtain ⟨hlt⟩ := andLeft (andRight hf)
  have hbelow := OriginalContextInsertionBelowCoreProof.successorStrict cutoff tailCount
    ⟨orderRight (suc cutoff) heCount hlt⟩
  obtain ⟨hiff⟩ := OriginalAllPositionContextDeleteConsProof.deleteConsIff
    gamma head tail cutoff freshDeleted deletedTail hc hcons
  obtain ⟨hd⟩ := hdel
  have hp : Nonempty (Derivation body Delta (graph2 deleteAt freshDeleted (suc cutoff) gamma)) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionRight hiff) hd⟩
  have heDeleted := valueUnique deleteAt freshDeleted deleted
    (Fin.cons (suc cutoff) (Fin.cons gamma Fin.elim0)) hp (andLeft (andRight (andRight hf)))
  have hca := outputTransport InternalListCodec.consCode freshDeleted deleted
    (Fin.cons head (Fin.cons deletedTail Fin.elim0)) heDeleted hcons
  obtain ⟨heD⟩ := lengthConsRecover deleted head deletedTail d td hca
    (andRight (andRight (andRight hf))) htd
  obtain ⟨heT⟩ := rowApply tailCount tail cutoff deletedTail td hrow
    (andIntro hlen (andIntro hbelow (andIntro hdel htd)))
  have he : Derivation body Delta (eqn tailCount d) := trans heT (symm heD)
  exact ⟨trans heCount (congSuc he)⟩

theorem successorAtCons (count gamma cutoff head tail deleted d : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row cutoff)))
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hf : Nonempty (Derivation body Delta (fields count gamma (suc cutoff) deleted d))) :
    Nonempty (Derivation body Delta (eqn count (suc d))) := by
  apply tailCases cutoff head tail _
  intro beta j Theta tailCount deletedTail freshDeleted hj hlen hdel hcons
  apply programCases length (Fin.cons deletedTail Fin.elim0) _
  intro beta' k Xi td hk htd
  simp only [consTermRename,emptyRename] at htd
  have hrow' := renameInto (renameInto hrow j Theta hj) k Xi hk
  simp only [rowRename] at hrow'
  have hc' := renameInto (renameInto hc j Theta hj) k Xi hk
  simp only [consGraphRename] at hc'
  have hf' := renameInto (renameInto hf j Theta hj) k Xi hk
  simp only [fieldsRename,sucRelabel] at hf'
  have hl' := renameInto hlen k Xi hk
  rw [lengthRename] at hl'
  have hd' := renameInto hdel k Xi hk
  rw [graph2Rename] at hd'
  have hs' := renameInto hcons k Xi hk
  rw [consGraphRename] at hs'
  simp only [eqnRename,sucRelabel]
  exact successorValues ((count.relabel j).relabel k) ((gamma.relabel j).relabel k)
    ((cutoff.relabel j).relabel k) ((head.relabel j).relabel k) ((tail.relabel j).relabel k)
    ((deleted.relabel j).relabel k) ((d.relabel j).relabel k)
    (tailCount.relabel k) (deletedTail.relabel k) (freshDeleted.relabel k) td
    hrow' hc' hf' hl' hd' hs' htd

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteLengthCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteLengthCoreProof
