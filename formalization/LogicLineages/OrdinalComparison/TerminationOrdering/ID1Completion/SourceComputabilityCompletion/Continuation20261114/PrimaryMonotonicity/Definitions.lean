module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open TwoSol20261113.CalibratedPrimary.Membership
/-- Inclusion of actual numeric-list members, quantified inside arithmetic.
It does not identify list codes or remove order/duplicates from the programs. -/
def included {alpha : Type} (left right : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock
    ((graph2 contains (numeral 1) (left.relabel Sum.inl) (.var (.inr (0 : Fin 1)))).imp
      (graph2 contains (numeral 1) (right.relabel Sum.inl) (.var (.inr (0 : Fin 1)))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity
