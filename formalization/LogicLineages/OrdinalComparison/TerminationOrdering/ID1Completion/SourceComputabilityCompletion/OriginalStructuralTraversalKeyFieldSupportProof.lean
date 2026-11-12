module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafTupleProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyFieldSupportProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- These projection laws leave every supplied representative opaque. -/
theorem transparentSource (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    (OriginalRankGuardedRepresentative.transparentInputs H G W p).base.oldSource =
      OriginalUniverseDecoder.source H G
        (InternalOriginalUniformContextMembership.contextMember p.base.member) W := rfl

theorem minimumMember (p : GlobalSourcePackage.Inputs) (H G : Program 1) (Q : Program 3) :
    (OriginalTransparentMinimum.minimumInputs H G Q p).base.member = p.base.member := rfl

theorem minimumWindow (p : GlobalSourcePackage.Inputs) (H G : Program 1) (Q : Program 3) :
    (OriginalTransparentMinimum.minimumInputs H G Q p).window = p.window := rfl

theorem refinedWindow (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    (OriginalFinalGuardedRank.refined p H G W).window = p.window := rfl

theorem rawRepresentative (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    (OriginalRankGuardedLeafTupleProof.rawData p H G W).oldRepresentative =
      (OriginalRankGuardedRepresentative.transparentInputs H G W p).base.oldRepresentative := rfl

theorem activation (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    OriginalActiveObservedClass.activation p H G W =
      OriginalRankGuardedRepresentative.active
        (OriginalUniverseDecoder.source H G
          (InternalOriginalUniformContextMembership.contextMember p.base.member) W) p.window := rfl

theorem kernelRepresentative (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) :
    (OriginalActiveKernelMinimum.inputs p H G W P).base.oldRepresentative =
      (OriginalRankGuardedRepresentative.transparentInputs H G W
        (OriginalTransparentMinimum.minimumInputs H G
          (OriginalActiveObservedClass.classTest p H G W
            OriginalRawSyntaxTransport.variableRankPackedRaw
            (OriginalActiveClassKernel.classTest p H G W P)) p)).base.oldRepresentative := rfl

theorem keyMember (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    (OriginalStructuralClassKeyDefinitions.inputs p H G W).base.member = p.base.member := rfl

theorem keySource (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    (OriginalStructuralClassKeyDefinitions.inputs p H G W).base.oldSource =
      OriginalUniverseDecoder.source H G
        (InternalOriginalUniformContextMembership.contextMember p.base.member) W := rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyFieldSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyFieldSupportProof
