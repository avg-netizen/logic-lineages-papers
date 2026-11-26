module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpansionEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpansionChildrenProof
open Source NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open OriginalHereditaryExpansion OriginalRawSyntaxTransport

theorem childrenValues {n : Nat} (c : Nat) (Gamma : List Ty) (q : Code (Fin n)) :
    childValues (codeNumber q) (Nat.pair c (Encodable.encode Gamma)) =
      (OriginalHereditaryWorkBound.children Gamma q).map (jobNumber c) := by
  cases q <;> simp [childValues,arityValue,tagValue,payloadValue,firstValue,secondValue,
    codeNumber,OriginalHereditaryWorkBound.children,jobNumber,Nat.unpair_pair,
    OriginalContextExtensionCalibrationProof.contextEncoding,
    OriginalContextExtensionCalibrationProof.typeEncoding,Nat.add_comm]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpansionChildrenProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpansionChildrenProof
