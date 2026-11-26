module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationTestsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedAllTestsDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalClosedPrograms (allBlock)
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalContextInsertion
open OriginalClassContextAllPositionObserver
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- The genuine original position test at every internally bounded cutoff.
The bound and all runtime inputs are arbitrary arithmetic terms. -/
def boundedMatrix {alpha : Type} (R : Program 2)
 (count seed candidate parameter : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
 (Below (.var (.inr 0)) (count.relabel Sum.inl)).imp
   (graph4 (positionTest R) (suc z) (.var (.inr 0))
     (seed.relabel Sum.inl) (candidate.relabel Sum.inl) (parameter.relabel Sum.inl))
def BoundedTests {alpha : Type} (R : Program 2)
 (count seed candidate parameter : OTerm alpha) : Formula alpha :=
 allBlock (boundedMatrix R count seed candidate parameter)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedAllTestsDefinitions
