module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionVariableAtProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionVariableAboveProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalListCodecSupportProof InternalRecursionClosureLogicProof
open InternalGraphCompositionFunctionalityProof InternalPositiveUnfoldingSupportProof
open InternalOriginalOrderSyntaxProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalContextInsertionVariableSupportProof OriginalContextInsertionShiftInductionProof
open OriginalContextInsertionVariableAtProof OriginalVariableDecoderGraphSupportProof

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

 theorem aboveAtGap (out typ index d cutoff gamma extended front suffix inserted gap : OTerm alpha)
    (hw : Nonempty (Derivation body Gamma
      (witnesses d cutoff gamma extended front suffix inserted)))
    (he : Nonempty (Derivation body Gamma (eqn (add cutoff gap) index))) :
    Nonempty (Derivation body Gamma
      ((OriginalVariableDecoder.graph out typ index gamma).iff
        (OriginalVariableDecoder.graph out typ (suc index) extended))) := by
  obtain ⟨he⟩ := he
  have h1 := variableIffInputs (body := body) (Gamma := Gamma) out typ index gamma (add cutoff gap) gamma
    ⟨symm he⟩ ⟨refl gamma⟩
  have h2 := appendShift front out typ cutoff suffix gamma gap (andLeft hw)
    (andLeft (andRight hw))
  have h3 := closedApply
    (OriginalVariableDecoderInternalProof.actualOriginalVariableDecoderConsSuccessor
      body alpha out typ gap inserted d suffix) (andLeft (andRight (andRight hw)))
  have h4 := appendShift front out typ cutoff inserted extended (suc gap) (andLeft hw)
    (andRight (andRight (andRight hw)))
  have h5 := variableIffInputs (body := body) (Gamma := Gamma) out typ (add cutoff (suc gap)) extended (suc index) extended
    ⟨trans (addSucc cutoff gap) (congSuc he)⟩ ⟨refl extended⟩
  exact iffTrans h1 (iffTrans h2 (iffTrans (iffSymm h3) (iffTrans (iffSymm h4) h5)))

 theorem aboveWitnesses (out typ index d cutoff gamma extended front suffix inserted : OTerm alpha)
    (hw : Nonempty (Derivation body Gamma
      (witnesses d cutoff gamma extended front suffix inserted)))
    (hn : Nonempty (Derivation body Gamma (Below index cutoff).not)) :
    Nonempty (Derivation body Gamma
      ((OriginalVariableDecoder.graph out typ index gamma).iff
        (OriginalVariableDecoder.graph out typ (suc index) extended))) := by
  apply InternalUnpairReverseSyntaxProof.weakOrderCases Gamma cutoff index _
    (InternalUnpairArithmeticProof.notLessWeak index cutoff hn)
  intro beta j Delta gap hj he
  rw [iffRename,graphRename,graphRename,sucRelabel]
  have hw' := renameInto hw j Delta hj
  rw [witnessesRename] at hw'
  exact aboveAtGap _ _ _ _ _ _ _ _ _ _ gap hw' he

 theorem variableAbove (out typ index d cutoff gamma extended : OTerm alpha)
    (hi : Nonempty (Derivation body Gamma (Insert d cutoff gamma extended)))
    (hn : Nonempty (Derivation body Gamma (Below index cutoff).not)) :
    Nonempty (Derivation body Gamma
      ((OriginalVariableDecoder.graph out typ index gamma).iff
        (OriginalVariableDecoder.graph out typ (suc index) extended))) := by
  apply insertCases d cutoff gamma extended _ hi
  intro beta j Delta front suffix inserted hj hw
  rw [iffRename,graphRename,graphRename,sucRelabel]
  have hn' := renameInto hn j Delta hj
  change Nonempty (Derivation body Delta ((ltF index cutoff).relabel j).not) at hn'
  rw [orderRename] at hn'
  exact aboveWitnesses _ _ _ _ _ _ _ front suffix inserted hw hn'

 theorem actualOriginalContextInsertionVariableAbove :
    OriginalContextInsertionTargets.ActualOriginalContextInsertionVariableAbove := by
  intro body alpha out typ index d cutoff gamma extended
  let A := Insert d cutoff gamma extended ⊓ (Below index cutoff).not
  have h : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := variableAbove out typ index d cutoff gamma extended (andLeft h) (andRight h)
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionVariableAboveProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionVariableAboveProof
