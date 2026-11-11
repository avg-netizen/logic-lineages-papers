module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelAppendInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelAppendProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalRecurrenceFuelSupportProof InternalAdditionLawsProof
open OriginalHereditaryValidityInternalRecurrenceFuelAppendInductionProof

 theorem actualOriginalHereditaryInternalWorkFuelAppend :
    OriginalHereditaryValidityInternalRecurrenceTargets.ActualOriginalHereditaryInternalWorkFuelAppend := by
  intro body alpha front suffix joined first second out
  let A := graph2 InternalApplicationValidityStackAppend.append joined front suffix ⊓
    (WorkFuelGraph first front ⊓ WorkFuelGraph second suffix)
  have h : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hv := appendValue front suffix joined first second
    (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
  obtain ⟨d⟩ := graphIffValue out (add first second) joined hv
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelAppendProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelAppendProof
