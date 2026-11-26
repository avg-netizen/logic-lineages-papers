module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesChildren.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentChildFields.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesChildren.NativeProof
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportSelectorProof OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalAcceptanceCalibrationProof

theorem childrenValue (x : Nat) : evaluate children (List.Vector.ofFn ![x]) =
    if arityValue x = 0 then 0 else if arityValue x = 2 then
      1 + Nat.pair (firstValue x) (1 + Nat.pair (secondValue x) 0)
    else 1 + Nat.pair (firstValue x) 0 := by
  simp only [children,singleton,double,evalBranch,sameOfEvaluation,constantEvaluation,
    arityOfEvaluation,consOfEvaluation,firstOfEvaluation,secondOfEvaluation]
  change (if arityValue x = 0 then 0 else
    if (if arityValue x = 2 then 1 else 0) = 0 then _ else _) = _
  by_cases h0 : arityValue x = 0 <;> by_cases h2 : arityValue x = 2 <;> simp [h0,h2]

theorem nativeChildren (n : Nat) (c : Code (Fin n)) :
    evaluate children (List.Vector.ofFn ![codeNumber c]) =
      NumberedMultisetNumeric.numbersNumber
        ((NumberedSyntaxBoundsPrimrecSupportProof.children c).map codeNumber) := by
  rw [childrenValue]
  cases c <;> simp [NumberedSyntaxBoundsPrimrecSupportProof.children,arityValue,firstValue,
    secondValue,tagValue,payloadValue,codeNumber,Nat.unpair_pair,NumberedMultisetNumeric.numbersNumber]

theorem nativeChildrenAndDecrease : Targets.NativeChildrenAndDecrease :=
  ⟨nativeChildren,NumberedSyntaxBoundsPrimrecSupportProof.childrenDecrease⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesChildren.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesChildren.NativeProof
