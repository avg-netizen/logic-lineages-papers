module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentTagFields.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentChildFields.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.EncodedMetadataFields.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentExchangeLayer.NativeProof
public import Mathlib.Tactic.FinCases
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem nativeFields : Targets.NativeFields := by
  intro n arity U V hU hV
  have hfields : ∀ i v, evaluate (fields U V i) v = TransparentExchangeLayer.fieldValue n arity i v := by
    intro i v
    have ht := TransparentTagFields.NativeProof.nativeTags n arity V hV v
    have hm0 := EncodedMetadataFields.NativeProof.nativeMetadata n arity V hV false v
    have hm1 := EncodedMetadataFields.NativeProof.nativeMetadata n arity V hV true v
    have hc0 := TransparentChildFields.NativeProof.nativeChildren n arity V hV false v
    have hc1 := TransparentChildFields.NativeProof.nativeChildren n arity V hV true v
    fin_cases i
    · simpa [fields] using ht.1
    · simpa [fields] using hm0.1
    · simpa [fields] using hm0.2.1
    · simpa [fields] using hm0.2.2.1
    · simpa [fields] using hm0.2.2.2
    · simpa [fields] using hc0.1
    · simpa [fields] using hc0.2
    · simpa [fields] using ht.2
    · simpa [fields] using hm1.1
    · simpa [fields] using hm1.2.1
    · simpa [fields] using hm1.2.2.1
    · simpa [fields] using hm1.2.2.2
    · simpa [fields] using hc1.1
    · simpa [fields] using hc1.2
    · simpa [fields] using hU 14 v
    · simpa [fields] using hU 15 v
    · simpa [fields] using hU 16 v
    · simpa [fields] using hU 17 v
    · simpa [fields] using hU 18 v
  exact ⟨hfields,TransparentExchangeLayer.NativeProof.nativeOptional n arity (fields U V) V
    (fun i _ _ v => hfields i v) hV⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.NativeProof
