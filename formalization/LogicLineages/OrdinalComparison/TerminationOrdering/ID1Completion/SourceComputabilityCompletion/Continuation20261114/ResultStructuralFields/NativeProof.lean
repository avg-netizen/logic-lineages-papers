module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ResultStructuralFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadResultFields.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ResultStructuralFields.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem nativeFields : Targets.NativeFields := by
  intro n arity U V hU hV
  have hs := (StructuralExchangeFields.NativeProof.nativeFields n arity U V hU hV).1
  have hf : ∀ i v, evaluate (fields U V i) v = TransparentExchangeLayer.fieldValue n arity i v := by
    intro i v
    by_cases hi : i = 17
    · subst i
      simpa [fields] using HeadResultFields.NativeProof.nativeResults n arity V hV false v
    · by_cases hj : i = 18
      · subst i
        simpa [fields] using HeadResultFields.NativeProof.nativeResults n arity V hV true v
      · simpa [fields,hi,hj] using hs i v
  exact ⟨hf,TransparentExchangeLayer.NativeProof.nativeOptional n arity (fields U V) V (fun i _ _ => hf i) hV⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ResultStructuralFields.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ResultStructuralFields.NativeProof
