module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SixSol20261113.Erasure.EvaluatorErasureDefinitions
/-- Literal raw-tag and packed-type selectors of an original packed input.
This does not use the tag of the recursive evaluator's output as a substitute. -/
def RootFields {alpha : Type} (input parameter tag typ : OTerm alpha) : Formula alpha :=
 graph2 OriginalRootObservation.tag tag input parameter ⊓
 graph1 InternalUnpair.left typ input
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentDefinitions
