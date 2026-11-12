module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedVisitDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotential
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport (constant)
/-- [frame,fixed global branching]. Visit=twice the actual job budget; every
nonzero-tag frame has cost one. Unknown tags still stall in the runtime, so
no progress theorem may omit the supported-frame/admissibility invariant. -/
def frameCost : Program 2 := InternalAcceptance.branch (leftOf (.projection 0))
 (.composition InternalArithmeticPrograms.addition
   ![.composition OriginalHereditaryBudgetSum.jobBudget ![rightOf (.projection 0),.projection 1],
     .composition OriginalHereditaryBudgetSum.jobBudget ![rightOf (.projection 0),.projection 1]])
 (constant 2 1)
/-- [head,recursive sum,fixed global branching]. -/
def sumStep : Program 3 := .composition InternalArithmeticPrograms.addition
 ![.composition frameCost ![.projection 0,.projection 2],.projection 1]
def agenda : Program 2 := InternalRawListRecursion.listRec (constant 1 0) sumStep
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotential
