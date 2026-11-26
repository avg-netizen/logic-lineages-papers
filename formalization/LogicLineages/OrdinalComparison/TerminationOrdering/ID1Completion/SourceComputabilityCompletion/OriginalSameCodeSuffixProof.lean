module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixObjectProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalQuotientSpineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineNonBottomProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixProof
open UniformCertificateCompletion OriginalSameCodeSuffixTargets

theorem actualOriginalSameCodeFinalPositivePathGuards :
    ActualOriginalSameCodeFinalPositivePathGuards := by
  intro p
  let q := OriginalSpineGuardLeaf.refineInputs p
  let r := OriginalApplicationSidecar.finalInputs q
  exact OriginalSameCodeSuffixInductionProof.positiveGuards
    (OuterSelection.data r.base r.window) r.window r.oldStep
    (OriginalQuotientSpineProof.actualOriginalFinalQuotientSpineGuard p)
    OriginalSpineNonBottomProof.actualOriginalSpineGuardRejectsBottom

theorem actualOriginalSameCodeFinalObjectSuffix : ActualOriginalSameCodeFinalObjectSuffix := by
  intro p
  let q := OriginalSpineGuardLeaf.refineInputs p
  let r := OriginalApplicationSidecar.finalInputs q
  change ∀ context : Nat, OriginalSameCodeSuffix.ObjectSuffix
    (OuterSelection.data r.base r.window) r.window r.oldStep (GlobalSourcePackage.source r) context
  intro context
  exact OriginalSameCodeSuffixObjectProof.objectSuffix r.oldSrc r.oldComp
    (OuterSelection.data r.base r.window) (RawScalar.checker (OuterSelection.data r.base r.window))
    r.oldStep r.window (actualOriginalSameCodeFinalPositivePathGuards p) context

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixProof
