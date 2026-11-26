module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangePathTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCertifiedPathConcatenationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangePathInductionDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTypedArgumentExchangePath
def result {alpha : Type} (observedSource observedTarget mapped : OTerm alpha) : Formula alpha :=
 InternalPathChecker.pathGraph OriginalNumericListSortExchange.edge observedSource observedTarget mapped
def fields (R : Program 2) {alpha : Type} (raw source target parameter observedSource observedTarget mapped : OTerm alpha) : Formula alpha :=
 InternalPathChecker.pathGraph OriginalTypedArgumentExchange.edge source target raw ⊓
 (graph2 (OriginalTypedArgumentObservations.argumentObservations R) observedSource source parameter ⊓
 (graph2 (OriginalTypedArgumentObservations.argumentObservations R) observedTarget target parameter ⊓ graph2 (mapPath R) mapped raw parameter))
def matrix (R : Program 2) {alpha : Type} (raw : OTerm alpha) : Formula (alpha ⊕ Fin 6) :=
 (fields R (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
   (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5))).imp
   (result (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5)))
def AtRaw (R : Program 2) {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix R raw)
def rawPredicate (R : Program 2) {alpha : Type} : Formula (alpha ⊕ Fin 1) := AtRaw R (.var (.inr 0))
def BelowRaw (R : Program 2) {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalStrongInduction.below (rawPredicate R) raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangePathInductionDefinitions
