module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableComputabilityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObjectSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationCoordinateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableComputabilityShapeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof (sucNeZeroApply)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem rawNonLambda (value : OTerm alpha)
    (hv : Nonempty (Derivation body Gamma
      (graph1 OriginalConstructorLeaf.variableTest InternalOriginalStepGuard.one value))) :
    Nonempty (Derivation body Gamma (OriginalNonLambdaApplication.nonLambda value)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons value Fin.elim0
  have hz := InternalStructuralEndpointGuardSupportProof.sameRightRecover
    (InternalApplicationStepPeel.constructorTag (.projection 0))
    (InternalAcceptance.constantZero 1) z xs hv (constantZeroValue xs)
  let P := OriginalConstructorShape.tagGraph InternalOriginalStepGuard.one value
  have hp : Nonempty (Derivation body (P :: Gamma) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨he⟩ := valueUnique OriginalConstructorShape.tag InternalOriginalStepGuard.one z xs
    hp (withHyp hz P)
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply he)⟩

theorem nonLambda (object : OTerm alpha)
    (hv : Nonempty (Derivation body Gamma (OriginalVariableObject.variableObject object))) :
    Nonempty (Derivation body Gamma (OriginalSourceNeutralApplication.nonLambdaObject object)) := by
  apply programCases InternalUnpair.right (Fin.cons object Fin.elim0) _
  intro beta j Delta payload hj hr
  rw [OriginalSourceNeutralApplicationSyntaxProof.nonLambdaObjectRename]
  have hv' := renameInto hv j Delta hj
  rw [OriginalVariableObjectSyntaxProof.variableObjectRename] at hv'
  simp only [consTermRename,emptyRename] at hr
  have hraw := OriginalVariableObjectSupportProof.variablePayloadRecover (object.relabel j) payload hv' hr
  exact OriginalSourceNeutralApplicationCoordinateProof.nonLambdaBackward
    (object.relabel j) payload hr (rawNonLambda payload hraw)

theorem actualOriginalVariableObjectNonLambda :
    OriginalVariableComputabilityTargets.ActualOriginalVariableObjectNonLambda := by
  intro body alpha Gamma object
  let H := OriginalVariableObject.variableObject object
  obtain ⟨h⟩ := nonLambda (body := body) (Gamma := H :: Gamma) object
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableComputabilityShapeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableComputabilityShapeProof
