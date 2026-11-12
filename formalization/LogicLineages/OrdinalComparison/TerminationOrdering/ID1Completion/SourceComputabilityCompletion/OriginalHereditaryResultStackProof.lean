module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryResultStackTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryResultStackProof
open OriginalHereditaryResultStack

theorem takePrefix (front tail : List Nat) : (front ++ tail).take front.length = front := by
 induction front with
 | nil => rfl
 | cons head front ih => simp [ih]

theorem dropPrefix (front tail : List Nat) : (front ++ tail).drop front.length = tail := by
 induction front with
 | nil => rfl
 | cons head front ih => simpa using ih

theorem getAfterPrefix (front tail : List Nat) (index : Nat) :
 (front ++ tail).getD (front.length + index) 0 = tail.getD index 0 := by
 induction front with
 | nil => rfl
 | cons head front ih => simpa [Nat.succ_add] using ih

theorem takeDeletions (children deletions old : List Nat) :
 (stack children deletions old).take deletions.length = deletions.reverse := by
 simpa only [stack,List.length_reverse,List.append_assoc] using takePrefix deletions.reverse (children.reverse ++ old)

theorem dropDeletions (children deletions old : List Nat) :
 (stack children deletions old).drop deletions.length = children.reverse ++ old := by
 simpa only [stack,List.length_reverse,List.append_assoc] using dropPrefix deletions.reverse (children.reverse ++ old)

theorem takeChildren (children deletions old : List Nat) :
 ((stack children deletions old).drop deletions.length).take children.length = children.reverse := by
 rw [dropDeletions]
 simpa only [List.length_reverse] using takePrefix children.reverse old

theorem restoreOld (children deletions old : List Nat) :
 (stack children deletions old).drop (deletions.length + children.length) = old := by
 simpa only [stack,List.length_append,List.length_reverse] using dropPrefix (deletions.reverse ++ children.reverse) old

theorem partition : OriginalHereditaryResultStackTargets.Partition := by
 intro children deletions old
 refine ⟨takeDeletions _ _ _, ?_, dropDeletions _ _ _,takeChildren _ _ _, ?_,restoreOld _ _ _⟩
 · rw [takeDeletions,List.reverse_reverse]
 · rw [takeChildren,List.reverse_reverse]

theorem stackGet (children deletions old : List Nat) (index : Nat) :
 (stack children deletions old).getD (deletions.length + index) 0 = (children.reverse ++ old).getD index 0 := by
 simpa only [stack,List.length_reverse,List.append_assoc] using getAfterPrefix deletions.reverse (children.reverse ++ old) index

theorem singletonLookup (value : Nat) (deletions old : List Nat) :
 (stack [value] deletions old).getD deletions.length 0 = value := by
 simpa using stackGet [value] deletions old 0

theorem binaryLookup (first second : Nat) (deletions old : List Nat) :
 (stack [first,second] deletions old).getD deletions.length 0 = second ∧
 (stack [first,second] deletions old).getD (deletions.length + 1) 0 = first := by
 constructor
 · simpa using stackGet [first,second] deletions old 0
 · simpa using stackGet [first,second] deletions old 1

theorem childSlots : OriginalHereditaryResultStackTargets.ChildSlots := by
 intro children deletions old hbound
 cases children with
 | nil => simp [firstSlot,secondSlot]
 | cons first rest =>
   cases rest with
   | nil => simpa [firstSlot,secondSlot] using congrArg (fun x : Nat => (x,0)) (singletonLookup first deletions old)
   | cons second rest =>
     cases rest with
     | nil =>
       have hindex : deletions.length + [first,second].length - 1 = deletions.length + 1 := by simp; omega
       obtain ⟨hsecond,hfirst⟩ := binaryLookup first second deletions old
       simp only [firstSlot,secondSlot,List.length_cons,List.length_nil] at *
       simp [hindex,hfirst,hsecond]
     | cons third rest => simp only [List.length_cons] at hbound; omega
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryResultStackProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryResultStackProof
