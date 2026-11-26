module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionShiftInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionVariableAtProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalListCodecSupportProof InternalRecursionClosureLogicProof
open InternalGraphCompositionFunctionalityProof InternalPositiveUnfoldingSupportProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalContextInsertionVariableSupportProof OriginalContextInsertionShiftInductionProof
open OriginalVariableDecoderGraphSupportProof

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

 theorem iffRename {beta : Type} (p q : Formula alpha) (j : alpha → beta) :
    (p.iff q).relabel j = (p.relabel j).iff (q.relabel j) := rfl

 theorem testRename {beta : Type} (out typ d : OTerm alpha) (j : alpha → beta) :
    (testSpec out typ d).relabel j = testSpec (out.relabel j) (typ.relabel j) (d.relabel j) := by
  simp only [testSpec,equalEqn]
  change ((eqn typ d).relabel j ⊓ (eqn out (suc z)).relabel j) ⊔
    (((eqn typ d).relabel j).not ⊓ (eqn out z).relabel j) = _
  simp only [eqnRelabel,sucRelabel,zRelabel]

 theorem atWitnesses (out typ d cutoff gamma extended front suffix inserted : OTerm alpha)
    (hw : Nonempty (Derivation body Gamma
      (witnesses d cutoff gamma extended front suffix inserted))) :
    Nonempty (Derivation body Gamma
      ((OriginalVariableDecoder.graph out typ cutoff extended).iff (testSpec out typ d))) := by
  have hs := appendShift front out typ cutoff inserted extended z (andLeft hw)
    (andRight (andRight (andRight hw)))
  have hi := variableIffInputs (body := body) (Gamma := Gamma) out typ cutoff extended (add cutoff z) extended
    ⟨symm (addZero cutoff)⟩ ⟨refl extended⟩
  have hz := closedApply
    (OriginalVariableDecoderInternalProof.actualOriginalVariableDecoderConsZero
      body alpha out typ inserted d suffix) (andLeft (andRight (andRight hw)))
  exact iffTrans hi (iffTrans hs hz)

 theorem variableAt (out typ d cutoff gamma extended : OTerm alpha)
    (hi : Nonempty (Derivation body Gamma (Insert d cutoff gamma extended))) :
    Nonempty (Derivation body Gamma
      ((OriginalVariableDecoder.graph out typ cutoff extended).iff (testSpec out typ d))) := by
  apply insertCases d cutoff gamma extended _ hi
  intro beta j Delta front suffix inserted hj hw
  rw [iffRename,graphRename,testRename]
  exact atWitnesses _ _ _ _ _ _ front suffix inserted hw

 theorem actualOriginalContextInsertionVariableAt :
    OriginalContextInsertionTargets.ActualOriginalContextInsertionVariableAt := by
  intro body alpha out typ d cutoff gamma extended
  obtain ⟨h⟩ := variableAt (body := body) (Gamma := [Insert d cutoff gamma extended])
    out typ d cutoff gamma extended ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionVariableAtProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionVariableAtProof
