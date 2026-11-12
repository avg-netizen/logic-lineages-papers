module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryResultStack
/-- Native list partition for a completed depth-first visit. This is not a
scheduler/evaluator transition or a replacement for the existing return AST. -/
def stack (children deletions old : List Nat) : List Nat := deletions.reverse ++ children.reverse ++ old
/-- Zero is explicit for absent slots, so old stack values are never mistaken
for missing completed children. Valid return frames have at most two children. -/
def firstSlot (children deletions old : List Nat) : Nat :=
 if children.length = 0 then 0 else (stack children deletions old).getD (deletions.length + children.length - 1) 0
def secondSlot (children deletions old : List Nat) : Nat :=
 if children.length = 2 then (stack children deletions old).getD deletions.length 0 else 0
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryResultStack
