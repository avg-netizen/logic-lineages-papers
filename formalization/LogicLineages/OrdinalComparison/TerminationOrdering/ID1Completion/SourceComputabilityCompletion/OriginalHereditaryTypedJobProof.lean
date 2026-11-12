module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobDeletionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobChildrenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedAuxiliaryCoding
open OriginalHereditaryAgendaDefinitions OriginalHereditaryWorkBound OriginalHereditaryTypedJobDefinitions
open OriginalHereditaryTypedJobTargets OriginalHereditaryTypedJobDecorationProof

theorem expansionClosure : ExpansionClosure := by
 intro n arity c a b ha hb
 rw [jobs,successors,decorateAppend] at hb
 rcases List.mem_append.mp hb with hc | hd
 · exact OriginalHereditaryTypedJobChildrenProof.childrenClosure a ha b hc
 · apply OriginalHereditaryTypedJobDeletionProof.deletionClosure a a.core.code [] a.core.context
     (0 + (children a.core.context a.core.code).length) ha ?_ b hd
   rw [Nat.zero_add,OriginalHereditaryTypedJobChildrenProof.childrenLength]

theorem returnShape : ReturnShape := by
 intro n arity a ha
 rcases a with ⟨role,typ,Gamma,code⟩
 cases ha with
 | term q => exact Or.inl rfl
 | arguments args =>
   apply Or.inr
   refine ⟨rfl,rfl,?_⟩
   cases args <;> simp [argumentsCode,codeNumber,OriginalRawSyntaxTransport.tagValue,Nat.unpair_pair]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobProof
