module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalNumericListSort OriginalNumericListSortExchange
open SourceComputabilityFormulaSupportProof (numeral)
def fields {alpha : Type} (raw source target left right : OTerm alpha) : Formula alpha :=
 graph3 (InternalPathChecker.checker edge false) (numeral 1) source target raw ⊓
   (graph1 sort left source ⊓ graph1 sort right target)
def matrix {alpha : Type} (raw : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
 (fields (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))).imp
   (equal (.var (.inr 2)) (.var (.inr 3)))
def AtRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix raw)
def rawPredicate {alpha : Type} : Formula (alpha ⊕ Fin 1) := AtRaw (.var (.inr 0))
def BelowRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalStrongInduction.below rawPredicate raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangePathDefinitions
