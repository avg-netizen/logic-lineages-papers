module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrefixTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrependInductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrefixInductionDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalNumericListSortExchange OriginalNumericListSortExchangePathPrefix
def result {alpha : Type} (newSource newTarget mapped : OTerm alpha) : Formula alpha :=
 InternalPathChecker.pathGraph edge newSource newTarget mapped
def fields {alpha : Type} (raw source target path newSource newTarget mapped : OTerm alpha) : Formula alpha :=
 InternalPathChecker.pathGraph edge source target path ⊓
 (graph2 InternalApplicationValidityStackAppend.append newSource raw source ⊓
 (graph2 InternalApplicationValidityStackAppend.append newTarget raw target ⊓ graph2 mapPrefix mapped raw path))
def matrix {alpha : Type} (raw : OTerm alpha) : Formula (alpha ⊕ Fin 6) :=
 (fields (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
   (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5))).imp
   (result (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5)))
def AtRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix raw)
def rawPredicate {alpha : Type} : Formula (alpha ⊕ Fin 1) := AtRaw (.var (.inr 0))
def BelowRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalStrongInduction.below rawPredicate raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathPrefixInductionDefinitions
