module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAlgebraTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortPrefixDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalNumericListSort
def fields {alpha : Type} (raw tailA tailB left right a b outA outB : OTerm alpha) : Formula alpha :=
 graph2 InternalApplicationValidityStackAppend.append left raw tailA ⊓ (graph2 InternalApplicationValidityStackAppend.append right raw tailB ⊓ (graph1 sort a tailA ⊓ (graph1 sort b tailB ⊓ (equal a b ⊓ (graph1 sort outA left ⊓ (graph1 sort outB right))))))
def matrix {alpha : Type} (raw : OTerm alpha) : Formula (alpha ⊕ Fin 8) :=
 (fields (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6)) (.var (.inr 7))).imp
 (equal (.var (.inr 6)) (.var (.inr 7)))
def AtRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix raw)
def rawPredicate {alpha : Type} : Formula (alpha ⊕ Fin 1) := AtRaw (.var (.inr 0))
def BelowRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalStrongInduction.below rawPredicate raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortPrefixDefinitions
