module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportExecutionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportNativeRecurrenceProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportSemanticProof OriginalRawSyntaxTransportExecutionProof
open NumberedMultisetNumeric

 theorem actualRawSyntaxNativeTermination : OriginalRawSyntaxTransportTargets.ActualRawSyntaxNativeTermination := by
  intro mode d k raw count h
  exact ⟨semanticFold mode d k raw, runAtSufficientCost mode d k raw count ((costFuelBound raw).trans h)⟩

 theorem foldSemantic (mode : Mode) (d k raw : Nat) : foldValue mode d k raw = semanticFold mode d k raw := by
  unfold foldValue runValue
  rw [runAtSufficientCost mode d k raw (fuelValue raw) (costFuelBound raw)]
  simp [outputValue, encodeState, InternalApplicationResultStack.encodeState, numbersNumber, Nat.add_comm 1]

 theorem actualRawSyntaxNativeRecurrence : OriginalRawSyntaxTransportTargets.ActualRawSyntaxNativeRecurrence := by
  intro mode d k raw
  simp only [foldSemantic]
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    have h1 : arityValue raw ≠ 1 := by omega
    have h2 : arityValue raw ≠ 2 := by omega
    rw [semanticEquation, if_neg h1, if_neg h2]
  · intro h1
    rw [semanticEquation, if_pos h1]
  · intro h2
    have h1 : arityValue raw ≠ 1 := by omega
    rw [semanticEquation, if_neg h1, if_pos h2]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportNativeRecurrenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportNativeRecurrenceProof
