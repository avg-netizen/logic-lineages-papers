module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionShiftSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionShiftCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalListCodecSupportProof InternalRecursionClosureLogicProof
open InternalGraphCompositionFunctionalityProof InternalPositiveUnfoldingSupportProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open OriginalContextInsertionSupportProof OriginalContextInsertionVariableSupportProof
open OriginalContextInsertionShiftSyntaxProof OriginalVariableDecoderGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

 theorem rowApply (front out typ count suffix joined index : OTerm alpha)
    (hrow : Nonempty (Derivation body Gamma (shiftRow front)))
    (hl : Nonempty (Derivation body Gamma (lengthGraph count front)))
    (ha : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append joined front suffix))) :
    Nonempty (Derivation body Gamma
      ((OriginalVariableDecoder.graph out typ (add count index) joined).iff
        (OriginalVariableDecoder.graph out typ index suffix))) := by
  have h := actualFiniteUniversalElimination body alpha 6 Gamma (shiftBody front)
    (fun i => emb (![out,typ,count,suffix,joined,index] i)) hrow
  rw [shiftWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hp⟩ := andIntro hl ha
  exact ⟨Derivation.implicationElimination h hp⟩

 theorem zeroCore (out typ count suffix joined index : OTerm alpha)
    (hl : Nonempty (Derivation body Gamma (lengthGraph count z)))
    (ha : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append joined z suffix))) :
    Nonempty (Derivation body Gamma
      ((OriginalVariableDecoder.graph out typ (add count index) joined).iff
        (OriginalVariableDecoder.graph out typ index suffix))) := by
  obtain ⟨hk⟩ := lengthNilRecover count hl
  have he : Nonempty (Derivation body Gamma (eqn (add count index) index)) :=
    ⟨trans (InternalOriginalOrderProof.congAddRight index hk) (leftZero index)⟩
  exact variableIffInputs out typ (add count index) joined index suffix he
    (InternalApplicationValidityStackAppendListProof.appendZeroRecover joined suffix ha)

 theorem consAtValues (front head tail out typ count tailCount suffix joined tailJoined index : OTerm alpha)
    (hrow : Nonempty (Derivation body Gamma (shiftRow tail)))
    (hc : Nonempty (Derivation body Gamma (consGraph front head tail)))
    (hl : Nonempty (Derivation body Gamma (lengthGraph count front)))
    (ht : Nonempty (Derivation body Gamma (lengthGraph tailCount tail)))
    (ha : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
    (hb : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append tailJoined tail suffix))) :
    Nonempty (Derivation body Gamma
      ((OriginalVariableDecoder.graph out typ (add count index) joined).iff
        (OriginalVariableDecoder.graph out typ index suffix))) := by
  obtain ⟨hk⟩ := lengthConsRecover front head tail count tailCount hc hl ht
  have he : Nonempty (Derivation body Gamma
      (eqn (add count index) (suc (add tailCount index)))) :=
    ⟨trans (InternalOriginalOrderProof.congAddRight index hk) (leftSuccessor tailCount index)⟩
  have hj := InternalApplicationValidityStackAppendListProof.consForward
    front head tail suffix tailJoined joined hc hb ha
  have hs := closedApply
    (OriginalVariableDecoderInternalProof.actualOriginalVariableDecoderConsSuccessor
      body alpha out typ (add tailCount index) joined head tailJoined) hj
  exact iffTrans (variableIffInputs out typ (add count index) joined
    (suc (add tailCount index)) joined he ⟨refl joined⟩)
    (iffTrans hs (rowApply tail out typ tailCount suffix tailJoined index hrow ht hb))

 theorem formulaIffRename {beta : Type} (p q : Formula alpha) (j : alpha → beta) :
    (p.iff q).relabel j = (p.relabel j).iff (q.relabel j) := rfl

 theorem consCore (front head tail out typ count suffix joined index : OTerm alpha)
    (hrow : Nonempty (Derivation body Gamma (shiftRow tail)))
    (hc : Nonempty (Derivation body Gamma (consGraph front head tail)))
    (hl : Nonempty (Derivation body Gamma (lengthGraph count front)))
    (ha : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append joined front suffix))) :
    Nonempty (Derivation body Gamma
      ((OriginalVariableDecoder.graph out typ (add count index) joined).iff
        (OriginalVariableDecoder.graph out typ index suffix))) := by
  apply programCases length (Fin.cons tail Fin.elim0) _
  intro beta j Delta tailCount hj ht
  apply programCases InternalApplicationValidityStackAppend.append
    (Fin.cons (tail.relabel j) (Fin.cons (suffix.relabel j) Fin.elim0)) _
  intro beta' k Theta tailJoined hk hb
  simp only [formulaIffRename,graphRename,InternalOriginalOrderSyntaxProof.addRelabel]
  have hrow' := renameInto (renameInto hrow j Delta hj) k Theta hk
  simp only [shiftRename] at hrow'
  have hc' := renameInto (renameInto hc j Delta hj) k Theta hk
  have hl' := renameInto (renameInto hl j Delta hj) k Theta hk
  have ha' := renameInto (renameInto ha j Delta hj) k Theta hk
  simp only [consGraphRename,lengthRename,graph2Rename] at hc' hl' ha'
  have ht' := renameInto ht k Theta hk
  simp only [programRename,consTermRename,emptyRename] at ht'
  simp only [consTermRename,emptyRename] at hb
  exact consAtValues _ _ _ _ _ _ (tailCount.relabel k) _ _ tailJoined _
    hrow' hc' hl' ht' ha' hb

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionShiftCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionShiftCoreProof
