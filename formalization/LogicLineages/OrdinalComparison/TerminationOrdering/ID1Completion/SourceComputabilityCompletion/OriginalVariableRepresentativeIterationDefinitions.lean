module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationIterationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescentDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeIteration
open OriginalVariableRepresentative
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalClosedPrograms (allBlock)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def leaf (data : Data) (window : Program 1) : Program 2 :=
  SpineApplicationIteration.leaf (baseData data window) window

def selectedValidity (data : Data) (window : Program 1) : Program 2 :=
  SpineApplicationIteration.selectedValidity (baseData data window) window

def step (data : Data) (window : Program 1) : Program 2 :=
  SpineApplicationIteration.step (baseData data window) window

def activeGraph {α : Type} (data : Data) (window : Program 1)
    (input parameter : OrdinaryArithmetic.Term α) : Formula α :=
  BottomRepresentative.activeGraph
    (SpineApplicationTargets.parameters (baseData data window) window) window input parameter

/-- Count and all four data coordinates vary INSIDE the actual arithmetic
induction formula. This is the original iterator, with only its observer
changed from the bottom indicator to the FULL original packed variable mark. -/
def iterationBody {α : Type} (data : Data) (window : Program 1)
    (count : OrdinaryArithmetic.Term α) : Formula (α ⊕ Fin 4) :=
  (InternalParameterizedNumericIteration.repeatGraph (step data window)
    (.var (.inr 1)) (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 2)) ⊓
    (activeGraph data window (.var (.inr 0)) (.var (.inr 2)) ⊓
      markGraph (.var (.inr 3)) (.var (.inr 0)))).imp
    (markGraph (.var (.inr 3)) (.var (.inr 1)))

def iterationRow {α : Type} (data : Data) (window : Program 1)
    (count : OrdinaryArithmetic.Term α) : Formula α :=
  allBlock (iterationBody data window count)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeIteration
