module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeIterationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFuelProgram
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport (constant succOf)
/-- Primitive recursion inputs are [depth,branching]; step inputs are
[previous depth,previous budget,branching]. -/
def budgetStep : Program 3 := succOf
 (.composition InternalArithmeticPrograms.multiplication ![.projection 2,.projection 1])
def budget : Program 2 := .recursion (constant 1 1) budgetStep
/-- Numeric annotated job is pair(role,pair(type,pair(raw,pair(window,context)))). -/
def rawJob : Program 1 := rightOf (rightOf (.projection 0))
def nodes : Program 1 := .composition OriginalStructuralNodeSize.raw (fun _ : Fin 1 => leftOf rawJob)
def contextLength : Program 1 := .composition OriginalContextInsertion.length
 (fun _ : Fin 1 => rightOf (rightOf rawJob))
def weight : Program 1 := .composition InternalArithmeticPrograms.addition
 ![contextLength,.composition InternalArithmeticPrograms.multiplication ![constant 1 2,nodes]]
def branching : Program 1 := succOf (succOf weight)
def fuel : Program 1 := .composition InternalArithmeticPrograms.multiplication
 ![constant 1 2,.composition budget ![weight,branching]]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFuelProgram
