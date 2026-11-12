module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFuelProgramDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteLengthTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalWeightDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
/-- Literal field selectors of the unchanged fuel Program. -/
def rawSelector : Program 1 := leftOf OriginalHereditaryFuelProgram.rawJob
def contextSelector : Program 1 := rightOf (rightOf OriginalHereditaryFuelProgram.rawJob)
def fields {alpha : Type} (job raw gamma : OTerm alpha) : Formula alpha :=
 graph1 rawSelector raw job ⊓ graph1 contextSelector gamma job
/-- Arithmetic normal form only; not a replacement for FuelProgram.weight. -/
def mass {alpha : Type} (len nodes : OTerm alpha) : OTerm alpha :=
 InternalAdditionLawsProof.add len (InternalAdditionLawsProof.add nodes nodes)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalWeightDefinitions
