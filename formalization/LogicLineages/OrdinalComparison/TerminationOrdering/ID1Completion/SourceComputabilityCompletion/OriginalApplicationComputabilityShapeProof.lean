module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComputabilityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationCoordinateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEdgeBridgeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineGuardLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineLeastProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSourceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComputabilityShapeProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z)
open InternalTagArithmeticSupportProof (cancelSuc sucNeZeroApply)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open UniformCertificateCompletion

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- The literal original application constructor has tag two, distinct from
lambda's tag one, regardless of its function child's shape. -/
theorem rawNonLambda (d e function argument out : OTerm alpha)
    (ha : Nonempty (Derivation body Gamma (graph4 application out d e function argument))) :
    Nonempty (Derivation body Gamma (OriginalNonLambdaApplication.nonLambda out)) := by
  let P := OriginalConstructorShape.tagGraph InternalOriginalStepGuard.one out
  have ht := andLeft (OriginalConstructorShapeApplicationProof.rawFields d e function argument out ha)
  have hp : Nonempty (Derivation body (P :: Gamma) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨he⟩ := valueUnique OriginalConstructorShape.tag positionTerm InternalOriginalStepGuard.one
    (Fin.cons out Fin.elim0) (withHyp ht P) hp
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply (cancelSuc he))⟩

/-- Bind only the actual original argument fold. The accepted own output
is the original constructor by the existing final actualJ equation. -/
theorem recoveredNonLambda (p : GlobalSourcePackage.Inputs)
    (context : Nat) (sigma tau : Ty)
    (F A X gammaCode function argument out parameter : OTerm alpha)
    (h : Nonempty (Derivation body Gamma
      (OriginalSourceNeutralApplication.Recovered
        (OuterSelection.data (OriginalApplicationSidecar.finalInputs p).base
          (OriginalApplicationSidecar.finalInputs p).window)
        (OriginalApplicationSidecar.finalInputs p).window
        (GlobalSourcePackage.computability (OriginalApplicationSidecar.finalInputs p))
        context sigma tau F A X gammaCode function argument out parameter))) :
    Nonempty (Derivation body Gamma (OriginalSourceNeutralApplication.nonLambdaObject X)) := by
  let r := OriginalApplicationSidecar.finalInputs p
  let data := OuterSelection.data r.base r.window
  apply programCases (InternalParameterizedCanonicalResultFold.foldN data)
    (Fin.cons argument (Fin.cons parameter Fin.elim0)) _
  intro beta j Delta argumentOut hj hn
  rw [OriginalSourceNeutralApplicationSyntaxProof.nonLambdaObjectRename]
  have h' := renameInto h j Delta hj
  rw [OriginalSourceNeutralApplicationSyntaxProof.recoveredRename] at h'
  simp only [consTermRename,emptyRename] at hn
  have ha := OriginalNeutralApplicationEdgeBridgeProof.finalForward p
    (SourceComputabilityFormulaSupportProof.numeral (NumberedLeastCodeRepresentative.typeNumber (.arrow sigma tau)))
    (SourceComputabilityFormulaSupportProof.numeral (NumberedLeastCodeRepresentative.typeNumber sigma))
    (SourceComputabilityFormulaSupportProof.numeral (NumberedLeastCodeRepresentative.typeNumber tau))
    (function.relabel j) (argument.relabel j) (out.relabel j) argumentOut (parameter.relabel j)
    (OriginalSourceNeutralApplicationFieldsProof.inputPremisesOf h') hn
    (OriginalSourceNeutralApplicationFieldsProof.actualJOf h')
  have hright := pairRight (X.relabel j) (gammaCode.relabel j) (out.relabel j)
    (OriginalSourceNeutralApplicationFieldsProof.outputPairOf h')
  exact OriginalSourceNeutralApplicationCoordinateProof.nonLambdaBackward (X.relabel j)
    (out.relabel j) hright (rawNonLambda _ _ _ _ _ ha)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComputabilityShapeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComputabilityShapeProof
