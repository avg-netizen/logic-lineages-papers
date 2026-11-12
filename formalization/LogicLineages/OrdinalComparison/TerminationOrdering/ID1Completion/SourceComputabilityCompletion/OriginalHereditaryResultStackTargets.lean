module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryResultStackDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryResultStackTargets
open OriginalHereditaryResultStack
/-- All lengths, with no two-child restriction. -/
def Partition : Prop := ∀ (children deletions old : List Nat),
 (stack children deletions old).take deletions.length = deletions.reverse ∧
 ((stack children deletions old).take deletions.length).reverse = deletions ∧
 (stack children deletions old).drop deletions.length = children.reverse ++ old ∧
 ((stack children deletions old).drop deletions.length).take children.length = children.reverse ∧
 (((stack children deletions old).drop deletions.length).take children.length).reverse = children ∧
 (stack children deletions old).drop (deletions.length + children.length) = old
/-- Native count-controlled slots only, not total evaluator correctness. -/
def ChildSlots : Prop := ∀ (children deletions old : List Nat), children.length ≤ 2 →
 (firstSlot children deletions old,secondSlot children deletions old) =
 (children.getD 0 0,children.getD 1 0)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryResultStackTargets
