module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeInputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeRootFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralVariableProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeGlobalProof
open OriginalConstructorShape OriginalConstructorShapeInputProof UniformCertificateCompletion

/-- One original input tuple precedes all refinements and all windows. Its
final source, computability and lift jointly supply the full Package, actual
full-fold root reflection, neutral-leaf law and original variable Object laws. -/
theorem actualOriginalConstructorShapeGlobalSelection :
    OriginalConstructorShapeTargets.ActualOriginalConstructorShapeGlobalSelection := by
  intro n arity
  obtain ⟨p,hp⟩ := GlobalSourcePackageProof.actualOriginalGlobalInputSelection n arity
  let q := OriginalNeutralLeaf.refineInputs (refineInputs p)
  let r := finalInputs p
  have hq : GlobalSourcePackage.InputsCalibrated n arity q :=
    OriginalNeutralLeafProof.refinedInputsCalibrated n arity (refineInputs p)
      (refinedInputsCalibrated n arity p hp)
  have hr : GlobalSourcePackage.InputsCalibrated n arity r := finalInputsCalibrated n arity p hp
  refine ⟨p,hp,hr,?_,?_,?_,?_⟩
  · exact (GlobalSourcePackageProof.actualOriginalGlobalSourcePackageConstruction n arity r hr).2.2
  · change FullFoldRootFields
      (OuterSelection.data (finalInputs p).base (finalInputs p).window) (finalInputs p).window
    rw [finalSelectedData,finalWindow]
    exact OriginalConstructorShapeRootFieldsProof.actualOriginalConstructorShapeRootFields p.base p.window
  · exact OriginalNeutralVariableProof.finalNeutralLaw (refineInputs p)
  · intro symbols S table hS
    exact ⟨OriginalVariableObjectCertificateProof.actualOriginalVariableObjectCertificateBottom
        n arity q hq symbols S table hS,
      OriginalVariableObjectLeastProof.actualOriginalVariableObjectLeast
        n arity q hq symbols S table hS⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeGlobalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeGlobalProof
