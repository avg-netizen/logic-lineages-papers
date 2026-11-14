module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.Induction
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary.Membership
def result {alpha : Type} (out needle : OTerm alpha) : Formula alpha := graph2 contains (numeral 1) out needle
def fields {alpha : Type} (E : Program 3) (count pool reached parameter out needle : OTerm alpha) : Formula alpha :=
  graph4 (iterate E) out count pool reached parameter ⊓ graph2 contains (numeral 1) reached needle
def matrix {alpha : Type} (E : Program 3) (count : OTerm alpha) : Formula (alpha ⊕ Fin 5) :=
  (fields E (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
    (.var (.inr 3)) (.var (.inr 4))).imp (result (.var (.inr 3)) (.var (.inr 4)))
def AtCount {alpha : Type} (E : Program 3) (count : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix E count)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.Induction
