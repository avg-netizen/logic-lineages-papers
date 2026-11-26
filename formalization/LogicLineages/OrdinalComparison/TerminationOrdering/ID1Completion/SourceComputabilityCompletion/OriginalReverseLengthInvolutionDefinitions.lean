module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseConsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseLengthInvolutionDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalClosedPrograms
open OriginalTypedArgumentObservations (reverse)
def fields {alpha : Type} (raw count mapped : OTerm alpha) : Formula alpha :=
 graph1 OriginalContextInsertion.length count raw ⊓ graph1 reverse mapped raw
def outputs {alpha : Type} (raw count mapped : OTerm alpha) : Formula alpha :=
 graph1 OriginalContextInsertion.length count mapped ⊓ graph1 reverse raw mapped
def matrix {alpha : Type} (raw : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
 (fields (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))).imp
 (outputs (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)))
def AtRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := allBlock (matrix raw)
def rawPredicate {alpha : Type} : Formula (alpha ⊕ Fin 1) := AtRaw (.var (.inr 0))
def BelowRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalStrongInduction.below rawPredicate raw

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseLengthInvolutionDefinitions
