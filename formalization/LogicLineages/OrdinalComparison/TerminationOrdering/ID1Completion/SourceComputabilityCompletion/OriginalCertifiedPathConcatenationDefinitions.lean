module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCertifiedPathConcatenationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCertifiedPathConcatenationDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def result (edge : Program 3) {alpha : Type} (source target combined : OTerm alpha) : Formula alpha :=
 InternalPathChecker.pathGraph edge source target combined
def fields (edge : Program 3) {alpha : Type} (raw source middle target right combined : OTerm alpha) : Formula alpha :=
 InternalPathChecker.pathGraph edge source middle raw ⊓
 (InternalPathChecker.pathGraph edge middle target right ⊓
 graph2 InternalApplicationValidityStackAppend.append combined raw right)
def matrix (edge : Program 3) {alpha : Type} (raw : OTerm alpha) : Formula (alpha ⊕ Fin 5) :=
 (fields edge (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4))).imp
 (result edge (.var (.inr 0)) (.var (.inr 2)) (.var (.inr 4)))
def AtRaw (edge : Program 3) {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix edge raw)
def rawPredicate (edge : Program 3) {alpha : Type} : Formula (alpha ⊕ Fin 1) := AtRaw edge (.var (.inr 0))
def BelowRaw (edge : Program 3) {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalStrongInduction.below (rawPredicate edge) raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCertifiedPathConcatenationDefinitions
