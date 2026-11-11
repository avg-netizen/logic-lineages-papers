module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalSourceInversionSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalListCodecSupportProof InternalRecursionClosureLogicProof
open InternalGraphCompositionFunctionalityProof InternalPositiveUnfoldingSupportProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof InternalSquareRootArithmeticSupportProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open OriginalContextInsertionSupportProof OriginalContextInsertionVariableSupportProof
open OriginalContextInsertionBelowSyntaxProof OriginalVariableDecoderGraphSupportProof

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

 theorem rowApply (front out typ count suffix joined index : OTerm alpha)
    (hrow : Nonempty (Derivation body Gamma (belowRow front)))
    (hl : Nonempty (Derivation body Gamma (lengthGraph count front)))
    (ha : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
    (hb : Nonempty (Derivation body Gamma (ltF index count))) :
    Nonempty (Derivation body Gamma
      ((OriginalVariableDecoder.graph out typ index joined).iff
        (OriginalVariableDecoder.graph out typ index front))) := by
  have h := actualFiniteUniversalElimination body alpha 6 Gamma (belowBody front)
    (fun i => emb (![out,typ,count,suffix,joined,index] i)) hrow
  rw [belowWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hp⟩ := andIntro hl (andIntro ha hb)
  exact ⟨Derivation.implicationElimination h hp⟩

 theorem zeroCore (out typ count joined index : OTerm alpha)
    (hl : Nonempty (Derivation body Gamma (lengthGraph count z)))
    (hb : Nonempty (Derivation body Gamma (ltF index count))) :
    Nonempty (Derivation body Gamma
      ((OriginalVariableDecoder.graph out typ index joined).iff
        (OriginalVariableDecoder.graph out typ index z))) := by
  obtain ⟨hk⟩ := lengthNilRecover count hl
  obtain ⟨hb⟩ := hb
  obtain ⟨hn⟩ := InternalLeastNumberProof.actualNothingBelowZero body alpha index
  exact ⟨Derivation.explosion (Derivation.implicationElimination
    (weakenClosed hn Gamma) (orderRight index hk hb))⟩

/-- Cancellation of the actual strict-order witness, not a metatheoretic
comparison of standard natural numbers. -/
 theorem successorStrict (index count : OTerm alpha)
    (hb : Nonempty (Derivation body Gamma (ltF (suc index) (suc count)))) :
    Nonempty (Derivation body Gamma (ltF index count)) := by
  apply orderCases Gamma (suc index) (suc count) _ hb
  intro beta j Delta gap hj he
  rw [orderRename]
  obtain ⟨he⟩ := he
  simp only [sucRelabel] at he
  apply actualOriginalOrderIntroduction body beta Delta (index.relabel j) (count.relabel j) gap
  rw [onEquality]
  exact ⟨cancelSuc (trans (symm (leftSuccessor (index.relabel j) (suc gap))) he)⟩

 theorem zeroAtCons (out typ front joined head tail tailJoined : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (consGraph front head tail)))
    (hj : Nonempty (Derivation body Gamma (consGraph joined head tailJoined))) :
    Nonempty (Derivation body Gamma
      ((OriginalVariableDecoder.graph out typ z joined).iff
        (OriginalVariableDecoder.graph out typ z front))) :=
  iffTrans
    (closedApply (OriginalVariableDecoderInternalProof.actualOriginalVariableDecoderConsZero
      body alpha out typ joined head tailJoined) hj)
    (iffSymm (closedApply
      (OriginalVariableDecoderInternalProof.actualOriginalVariableDecoderConsZero
        body alpha out typ front head tail) hf))

 theorem successorAtCons
    (front head tail out typ count tailCount suffix joined tailJoined index : OTerm alpha)
    (hrow : Nonempty (Derivation body Gamma (belowRow tail)))
    (hc : Nonempty (Derivation body Gamma (consGraph front head tail)))
    (hj : Nonempty (Derivation body Gamma (consGraph joined head tailJoined)))
    (hl : Nonempty (Derivation body Gamma (lengthGraph count front)))
    (ht : Nonempty (Derivation body Gamma (lengthGraph tailCount tail)))
    (ha : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append tailJoined tail suffix)))
    (hb : Nonempty (Derivation body Gamma (ltF (suc index) count))) :
    Nonempty (Derivation body Gamma
      ((OriginalVariableDecoder.graph out typ (suc index) joined).iff
        (OriginalVariableDecoder.graph out typ (suc index) front))) := by
  obtain ⟨hk⟩ := lengthConsRecover front head tail count tailCount hc hl ht
  obtain ⟨hb⟩ := hb
  have hs := successorStrict index tailCount ⟨orderRight (suc index) hk hb⟩
  have hr := rowApply tail out typ tailCount suffix tailJoined index hrow ht ha hs
  have hjv := closedApply
    (OriginalVariableDecoderInternalProof.actualOriginalVariableDecoderConsSuccessor
      body alpha out typ index joined head tailJoined) hj
  have hfv := closedApply
    (OriginalVariableDecoderInternalProof.actualOriginalVariableDecoderConsSuccessor
      body alpha out typ index front head tail) hc
  exact iffTrans hjv (iffTrans hr (iffSymm hfv))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowCoreProof
