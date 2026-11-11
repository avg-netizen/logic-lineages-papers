module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportCodeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportTypedSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportTypedProof
open Source NumberedAuxiliaryCoding NumberedRewriteSyntax NumberedLeastCodeRepresentative
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportCodeProof OriginalRawSyntaxTransportTypedSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

 theorem actualRawSyntaxTypedCalibration : OriginalRawSyntaxTransportTargets.ActualRawSyntaxTypedCalibration := by
  intro n arity binders Gamma sigma tau
  refine ⟨?_, ?_, ?_⟩
  · intro q
    rw [actualRawSyntaxCodeCalibration.1 n binders.length (termCode q)]
    exact congrArg codeNumber
      (NumberedAuxiliaryShiftSupportProof.typedShiftCalibration (Fin n) arity binders Gamma sigma tau q).symm
  · intro q
    rw [actualRawSyntaxCodeCalibration.2.1 n binders.length sigma (termCode q)]
    exact congrArg codeNumber (typedErasure binders Gamma sigma tau q).symm
  · intro q
    rw [actualRawSyntaxCodeCalibration.2.2 n (termCode q)]
    exact typedVariableCount q

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportTypedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportTypedProof
