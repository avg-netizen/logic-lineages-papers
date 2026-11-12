module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAlgebraTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortOriginalDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalNumericListSort

def fields {alpha : Type} (raw x state : OTerm alpha) : Formula alpha := graph2 insertState state raw x
def matrix {alpha : Type} (raw : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
 (fields (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))).imp
 (graph1 InternalUnpair.left (raw.relabel Sum.inl) (.var (.inr 1)))
def AtRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix raw)
def rawPredicate {alpha : Type} : Formula (alpha ⊕ Fin 1) := AtRaw (.var (.inr 0))
def BelowRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalStrongInduction.below rawPredicate raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortOriginalDefinitions
