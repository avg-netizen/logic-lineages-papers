module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalAccumulatorDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseAccumulatorCompatibilityDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalClosedPrograms
open OriginalTypedArgumentObservationsReverseInternalAccumulatorDefinitions (accumulated)
def fields {alpha : Type} (raw acc1 acc2 suffix left right : OTerm alpha) : Formula alpha :=
 graph2 InternalApplicationValidityStackAppend.append acc2 acc1 suffix ⊓
 (graph2 accumulated left raw acc1 ⊓ graph2 accumulated right raw acc2)
def matrix {alpha : Type} (raw : OTerm alpha) : Formula (alpha ⊕ Fin 5) :=
 (fields (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
   (.var (.inr 3)) (.var (.inr 4))).imp
 (graph2 InternalApplicationValidityStackAppend.append (.var (.inr 4)) (.var (.inr 3)) (.var (.inr 2)))
def AtRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := allBlock (matrix raw)
def rawPredicate {alpha : Type} : Formula (alpha ⊕ Fin 1) := AtRaw (.var (.inr 0))
def BelowRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalStrongInduction.below rawPredicate raw

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseAccumulatorCompatibilityDefinitions
