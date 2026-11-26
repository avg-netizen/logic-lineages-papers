module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyFieldSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyFieldsProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem representative (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) :
    (OriginalStructuralClassKeyDefinitions.inputs p H G W).base.oldRepresentative =
      OriginalStructuralClassKeyDefinitions.key p H G W := rfl

theorem source (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) :
    (OriginalRankGuardedRepresentative.transparentInputs H G W
      (OriginalStructuralTraversalKey.minimumInputs p H G W P)).base.oldSource =
      (OriginalStructuralClassKeyDefinitions.inputs p H G W).base.oldSource := by
  rw [OriginalStructuralTraversalKeyFieldSupportProof.transparentSource]
  unfold OriginalStructuralTraversalKey.minimumInputs
  rw [OriginalStructuralTraversalKeyFieldSupportProof.minimumMember,
    OriginalStructuralTraversalKeyFieldSupportProof.keyMember,
    OriginalStructuralTraversalKeyFieldSupportProof.keySource]

theorem activation (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) :
    OriginalActiveObservedClass.activation (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W =
      OriginalRankGuardedRepresentative.active
        (OriginalStructuralClassKeyDefinitions.inputs p H G W).base.oldSource
        (OriginalStructuralClassKeyDefinitions.inputs p H G W).window := by
  rw [OriginalStructuralTraversalKeyFieldSupportProof.activation,
    OriginalStructuralTraversalKeyFieldSupportProof.keyMember,
    OriginalStructuralTraversalKeyFieldSupportProof.keySource]

theorem window (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) :
    (OriginalStructuralTraversalKey.refined p H G W P).window =
      (OriginalStructuralClassKeyDefinitions.inputs p H G W).window := by
  unfold OriginalStructuralTraversalKey.refined
  rw [OriginalStructuralTraversalKeyFieldSupportProof.refinedWindow]
  unfold OriginalStructuralTraversalKey.minimumInputs
  exact OriginalStructuralTraversalKeyFieldSupportProof.minimumWindow _ _ _ _

theorem rawRepresentative (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) :
    (OriginalRankGuardedLeafTupleProof.rawData
      (OriginalStructuralTraversalKey.minimumInputs p H G W P) H G W).oldRepresentative =
      (OriginalActiveKernelMinimum.inputs (OriginalStructuralClassKeyDefinitions.inputs p H G W)
        H G W P).base.oldRepresentative := by
  rw [OriginalStructuralTraversalKeyFieldSupportProof.rawRepresentative,
    OriginalStructuralTraversalKeyFieldSupportProof.kernelRepresentative]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyFieldsProof
