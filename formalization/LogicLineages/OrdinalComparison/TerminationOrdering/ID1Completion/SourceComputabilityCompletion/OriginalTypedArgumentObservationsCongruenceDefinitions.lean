module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelNumericSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruence
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalGraphComposition
open InternalApplicationCertificateConstructors InternalClosedPrograms
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Literal internal pointwise agreement at the SAME runtime parameter.
No source predicate or native evaluation is part of this formula. -/
def agreementBody {alpha : Type} (R S : Program 2) (parameter : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
 (graph2 R (.var (.inr 1)) (.var (.inr 0)) (parameter.relabel Sum.inl) ⊓
  graph2 S (.var (.inr 2)) (.var (.inr 0)) (parameter.relabel Sum.inl)).imp
   (equal (.var (.inr 1)) (.var (.inr 2)))
def Agreement {alpha : Type} (R S : Program 2) (parameter : OTerm alpha) : Formula alpha :=
 allBlock (agreementBody R S parameter)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruence
