module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryResultStackProgramDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryResultStackProgramTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedMultisetNumeric
/-- Native calibration of actual selector Programs. No evaluator termination
or internal graph reflection is asserted. -/
def Calibration : Prop := ∀ (children deletions old : List Nat), children.length ≤ 2 →
 let v := List.Vector.ofFn ![children.length,deletions.length,
   numbersNumber (OriginalHereditaryResultStack.stack children deletions old)]
 evaluate OriginalHereditaryResultStackProgram.firstSlot v = children.getD 0 0 ∧
 evaluate OriginalHereditaryResultStackProgram.secondSlot v = children.getD 1 0 ∧
 evaluate OriginalHereditaryResultStackProgram.deletionRow v = numbersNumber deletions ∧
 evaluate OriginalHereditaryResultStackProgram.oldSuffix v = numbersNumber old
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryResultStackProgramTargets
