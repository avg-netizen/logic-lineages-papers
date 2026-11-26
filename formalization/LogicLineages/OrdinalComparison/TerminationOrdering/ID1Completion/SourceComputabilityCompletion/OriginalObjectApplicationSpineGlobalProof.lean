module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalObjectApplicationSpineGlobalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalObjectApplicationSpineGlobalPropertiesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineGuardLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalObjectApplicationSpineGlobalProof
open UniformCertificateCompletion

/-- Choose one original calibrated input tuple. Its all-input-equal leaf
refinement and unchanged final pipeline supply the complete Object/global
conjunction and the raw-step guard at exactly the same final tuple. -/
theorem actualOriginalObjectApplicationSpineGlobalSelection :
    OriginalObjectApplicationSpineGlobalTargets.ActualOriginalObjectApplicationSpineGlobalSelection := by
  intro n arity
  obtain ⟨p,hp⟩ := GlobalSourcePackageProof.actualOriginalGlobalInputSelection n arity
  let q := OriginalSpineGuardLeaf.refineInputs p
  have hq : GlobalSourcePackage.InputsCalibrated n arity q :=
    OriginalSpineGuardLeafProof.refinedInputsCalibrated n arity p hp
  refine ⟨p,hp,?_,hq,
    OriginalObjectApplicationSpineGlobalPropertiesProof.properties n arity q hq,
    OriginalSelectedStepSpineProof.actualOriginalFinalRawStepSpineGuard p⟩
  exact OriginalSpineGuardLeafEvaluationProof.actualOriginalSpineGuardLeafRefinementEquality
    n arity p.oldStep hp.2.2.2.2.1

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalObjectApplicationSpineGlobalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalObjectApplicationSpineGlobalProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalObjectApplicationSpineGlobalProof.actualOriginalObjectApplicationSpineGlobalSelection
