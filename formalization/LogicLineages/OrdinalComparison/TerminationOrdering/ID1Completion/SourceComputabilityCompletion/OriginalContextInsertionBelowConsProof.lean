module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowConsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalListCodecSupportProof InternalRecursionClosureLogicProof
open InternalGraphCompositionFunctionalityProof InternalPositiveUnfoldingSupportProof
open InternalOriginalOrderSyntaxProof InternalSquareRootArithmeticSupportProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open OriginalContextInsertionSupportProof OriginalContextInsertionVariableSupportProof
open OriginalContextInsertionBelowSyntaxProof OriginalContextInsertionBelowCoreProof
open OriginalVariableDecoderGraphSupportProof

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

 theorem consAtValues
    (front head tail out typ count tailCount suffix joined tailJoined index : OTerm alpha)
    (hrow : Nonempty (Derivation body Gamma (belowRow tail)))
    (hc : Nonempty (Derivation body Gamma (consGraph front head tail)))
    (hl : Nonempty (Derivation body Gamma (lengthGraph count front)))
    (ht : Nonempty (Derivation body Gamma (lengthGraph tailCount tail)))
    (ha : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
    (hd : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append tailJoined tail suffix)))
    (hb : Nonempty (Derivation body Gamma (ltF index count))) :
    Nonempty (Derivation body Gamma
      ((OriginalVariableDecoder.graph out typ index joined).iff
        (OriginalVariableDecoder.graph out typ index front))) := by
  have hj := InternalApplicationValidityStackAppendListProof.consForward
    front head tail suffix tailJoined joined hc hd ha
  apply zeroSuccessorCases Gamma index _
  · have hz : Nonempty (Derivation body (eqn index z :: Gamma) (eqn index z)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hi := variableIffInputs out typ index joined z joined hz ⟨refl joined⟩
    have hf := variableIffInputs out typ index front z front hz ⟨refl front⟩
    have hm := zeroAtCons out typ front joined head tail tailJoined (withHyp hc (eqn index z)) (withHyp hj (eqn index z))
    exact iffTrans hi (iffTrans hm (iffSymm hf))
  · intro beta j Delta predecessor hk he
    rw [iffRename,graphRename,graphRename]
    have hrow' := renameInto hrow j Delta hk
    rw [belowRename] at hrow'
    have hc' := renameInto hc j Delta hk
    have hj' := renameInto hj j Delta hk
    simp only [consGraphRename] at hc' hj'
    have hl' := renameInto hl j Delta hk
    have ht' := renameInto ht j Delta hk
    simp only [lengthRename] at hl' ht'
    have hd' := renameInto hd j Delta hk
    rw [graph2Rename] at hd'
    have hb' := renameInto hb j Delta hk
    rw [orderRename] at hb'
    obtain ⟨hb'⟩ := hb'
    obtain ⟨he⟩ := he
    have hm := successorAtCons (front.relabel j) (head.relabel j) (tail.relabel j)
      (out.relabel j) (typ.relabel j) (count.relabel j) (tailCount.relabel j)
      (suffix.relabel j) (joined.relabel j) (tailJoined.relabel j) predecessor
      hrow' hc' hj' hl' ht' hd' ⟨orderLeft (count.relabel j) he hb'⟩
    have hi := variableIffInputs (out.relabel j) (typ.relabel j) (index.relabel j)
      (joined.relabel j) (suc predecessor) (joined.relabel j) ⟨he⟩ ⟨refl _⟩
    have hf := variableIffInputs (out.relabel j) (typ.relabel j) (index.relabel j)
      (front.relabel j) (suc predecessor) (front.relabel j) ⟨he⟩ ⟨refl _⟩
    exact iffTrans hi (iffTrans hm (iffSymm hf))

 theorem consCore (front head tail out typ count suffix joined index : OTerm alpha)
    (hrow : Nonempty (Derivation body Gamma (belowRow tail)))
    (hc : Nonempty (Derivation body Gamma (consGraph front head tail)))
    (hl : Nonempty (Derivation body Gamma (lengthGraph count front)))
    (ha : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
    (hb : Nonempty (Derivation body Gamma (ltF index count))) :
    Nonempty (Derivation body Gamma
      ((OriginalVariableDecoder.graph out typ index joined).iff
        (OriginalVariableDecoder.graph out typ index front))) := by
  apply programCases length (Fin.cons tail Fin.elim0) _
  intro beta j Delta tailCount hj ht
  apply programCases InternalApplicationValidityStackAppend.append
    (Fin.cons (tail.relabel j) (Fin.cons (suffix.relabel j) Fin.elim0)) _
  intro beta' k Theta tailJoined hk hd
  simp only [iffRename,graphRename]
  have hrow' := renameInto (renameInto hrow j Delta hj) k Theta hk
  simp only [belowRename] at hrow'
  have hc' := renameInto (renameInto hc j Delta hj) k Theta hk
  have hl' := renameInto (renameInto hl j Delta hj) k Theta hk
  have ha' := renameInto (renameInto ha j Delta hj) k Theta hk
  simp only [consGraphRename,lengthRename,graph2Rename] at hc' hl' ha'
  have hb' := renameInto (renameInto hb j Delta hj) k Theta hk
  simp only [orderRename] at hb'
  have ht' := renameInto ht k Theta hk
  simp only [programRename,consTermRename,emptyRename] at ht'
  simp only [consTermRename,emptyRename] at hd
  exact consAtValues _ _ _ _ _ _ (tailCount.relabel k) _ _ tailJoined _
    hrow' hc' hl' ht' ha' hd hb'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowConsProof
