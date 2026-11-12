module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFuelProgramDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSum
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
/-- Auxiliary proof measure only. Input order [job,fixed global branching]. -/
def jobBudget : Program 2 := .composition OriginalHereditaryFuelProgram.budget
 ![.composition OriginalHereditaryFuelProgram.weight (fun _ : Fin 1 => .projection 0),.projection 1]
/-- Original listRec step [head,recursive suffix sum,fixed global branching]. -/
def sumStep : Program 3 := .composition InternalArithmeticPrograms.addition
 ![.composition jobBudget ![.projection 0,.projection 2],.projection 1]
/-- Actual numeric sum over every job; no runtime or fuel AST is replaced. -/
def sum : Program 2 := InternalRawListRecursion.listRec (OriginalRawSyntaxTransport.constant 1 0) sumStep
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSum
