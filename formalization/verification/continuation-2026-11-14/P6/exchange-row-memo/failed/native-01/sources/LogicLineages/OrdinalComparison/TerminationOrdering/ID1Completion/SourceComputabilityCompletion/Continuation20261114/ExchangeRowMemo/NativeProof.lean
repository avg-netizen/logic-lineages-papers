module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeRowMemo.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeRowMemo.NativeProof
open NumberedExchangeCodeFieldsProof NumberedSyntaxBoundsPrimrecSupportProof

theorem originalBinaryDependencies : Targets.OriginalBinaryDependencies := by
  intro n source target x0 x1 y0 y1 hs ht
  simp only [dependencies,hs,ht,NumberedCodeEnumerationPrimrecSupportProof.cross,
    List.flatMap_cons,List.flatMap_nil,List.map_cons,List.map_nil,List.cons_append,List.nil_append]

theorem originalDependencyBounds : Targets.OriginalDependencyBounds := by
  intro n source target x y h
  have hs := dependenciesDecrease n (source,target) (x,y) h
  obtain ⟨a,ha,hb⟩ := List.mem_flatMap.mp h
  obtain ⟨c,hc,he⟩ := List.mem_map.mp hb
  cases he
  exact ⟨hs,childrenDecrease n target c hc⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeRowMemo.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeRowMemo.NativeProof
