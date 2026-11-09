module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomRepresentativeDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescent
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open SourceComputabilityCompletion.BottomRepresentative
open InternalApplicationCertificateConstructors
open InternalClosedPrograms (allBlock)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The validator is literally that of the eventual globally selected tuple.
It is independent of the oldRepresentative field changed by the wrapper. -/
def selectedValidity (data : InternalOriginalUniformDescentSelection.Data)
    (window : Program 1) : Program 2 :=
  InternalOriginalUniformDescentSelection.validity (readyData data window)

def step (data : InternalOriginalUniformDescentSelection.Data)
    (window : Program 1) : Program 2 :=
  InternalParameterizedBoundedDescentNormalizer.transition
    (representative data window) (selectedValidity data window)

/-- The four bound terms are [input,out,parameter,indicator]. Keeping them
inside the row permits the actual internal induction to vary the next value. -/
def iterationBody {α : Type} (data : InternalOriginalUniformDescentSelection.Data)
    (window : Program 1) (count : OrdinaryArithmetic.Term α) : Formula (α ⊕ Fin 4) :=
  (InternalParameterizedNumericIteration.repeatGraph (step data window)
    (.var (.inr 1)) (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 2)) ⊓
    (activeGraph data window (.var (.inr 0)) (.var (.inr 2)) ⊓
      bottomGraph (.var (.inr 3)) (.var (.inr 0)))).imp
    (bottomGraph (.var (.inr 3)) (.var (.inr 1)))

def iterationRow {α : Type} (data : InternalOriginalUniformDescentSelection.Data)
    (window : Program 1) (count : OrdinaryArithmetic.Term α) : Formula α :=
  allBlock (iterationBody data window count)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescent
