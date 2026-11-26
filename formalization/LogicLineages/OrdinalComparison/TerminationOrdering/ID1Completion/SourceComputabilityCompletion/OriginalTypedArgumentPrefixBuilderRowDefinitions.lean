module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilderTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilderRowDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTypedArgumentPrefixBuilder OriginalTypedArgumentObservations
def fields {alpha : Type} (R : Program 2) (raw suffix built parameter mappedValue suffixValue total : OTerm alpha) : Formula alpha :=
 graph2 build built raw suffix ⊓ (graph2 (mapped R) mappedValue raw parameter ⊓
 (graph2 (argumentObservations R) suffixValue suffix parameter ⊓
 graph2 InternalApplicationValidityStackAppend.append total mappedValue suffixValue))
def matrix {alpha : Type} (R : Program 2) (raw : OTerm alpha) : Formula (alpha ⊕ Fin 6) :=
 (fields R (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
   (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5))).imp
 (graph2 (argumentObservations R) (.var (.inr 5)) (.var (.inr 1)) (.var (.inr 2)))
def AtRaw {alpha : Type} (R : Program 2) (raw : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix R raw)
def rawPredicate {alpha : Type} (R : Program 2) : Formula (alpha ⊕ Fin 1) := AtRaw R (.var (.inr 0))
def BelowRaw {alpha : Type} (R : Program 2) (raw : OTerm alpha) : Formula alpha := InternalStrongInduction.below (rawPredicate R) raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilderRowDefinitions
