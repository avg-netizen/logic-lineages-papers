module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryResultStackTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionObserverDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryResultStackProgram
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport (constant)
/-- Inputs [child count,deletion count,encoded result stack]. These selectors
are total on all numeric inputs; count calibration is proved separately. -/
def totalCount : Program 3 := .composition InternalArithmeticPrograms.addition ![.projection 1,.projection 0]
def firstIndex : Program 3 := .composition InternalEqualityTest.predecessor (fun _ : Fin 1 => totalCount)
def firstSlot : Program 3 := InternalAcceptance.branch (.projection 0) (constant 3 0)
 (.composition InternalRawListRecursion.lookup ![firstIndex,.projection 2])
def secondSlot : Program 3 := OriginalTypedDecoder.ifSame (.projection 0) (constant 3 2)
 (.composition InternalRawListRecursion.lookup ![.projection 1,.projection 2]) (constant 3 0)
def deletionFront : Program 3 := .composition OriginalClassContextAllPositionObserver.front ![.projection 1,.projection 2]
def deletionRow : Program 3 := .composition OriginalTypedArgumentObservations.reverse (fun _ : Fin 1 => deletionFront)
def oldSuffix : Program 3 := .composition InternalRawListRecursion.drop ![totalCount,.projection 2]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryResultStackProgram
