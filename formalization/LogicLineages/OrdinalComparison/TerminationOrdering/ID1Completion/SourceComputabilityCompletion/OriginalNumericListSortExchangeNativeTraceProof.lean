module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeNativeTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeNativeTraceProof
open OriginalNumericListSortExchangeNative
theorem prepend (h : Nat) {xs ys ms} (ht : Trace xs ys ms) :
 Trace (h :: xs) (h :: ys) (ms.map (Move.prepend h)) := by
 induction ht with
 | nil xs => exact .nil _
 | cons m ht ih => exact Trace.cons (m.prepend h) ih

theorem append {xs ys zs left right} (hl : Trace xs ys left) (hr : Trace ys zs right) :
 Trace xs zs (left ++ right) := by
 induction hl generalizing zs right with
 | nil xs => exact hr
 | cons m ht ih => exact .cons m (ih hr)

theorem fromPermutation {xs ys : List Nat} (h : xs.Perm ys) :
 ∃ moves : List Move, Trace xs ys moves := by
 induction h with
 | nil => exact ⟨[],.nil []⟩
 | cons h hp ih =>
   obtain ⟨ms,ht⟩ := ih
   exact ⟨ms.map (Move.prepend h),prepend h ht⟩
 | swap a b rest => exact ⟨[⟨[],b,a,rest⟩],.cons ⟨[],b,a,rest⟩ (.nil _)⟩
 | trans hp hq ihp ihq =>
   obtain ⟨ms,hm⟩ := ihp
   obtain ⟨ns,hn⟩ := ihq
   exact ⟨ms ++ ns,append hm hn⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeNativeTraceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeNativeTraceProof
