module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescentDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomApplicationTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open SourceComputabilityCompletion.BottomRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- SAME actualJ and same globally selected canonical tuple. These are the
ORIGINAL generic application-typing premises, plus activation of the window
at that same parameter. No function-normalization fixedness, child successful
run, extra shape contract, semantic calibration or accessibility is assumed. -/
def ActualParameterizedApplicationNonBottom : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (window : Program 1)
    (α : Type) (Delta : List (Formula α))
    (arrow domain codomain function argument out parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((graph2 (windowAt window) InternalOriginalStepGuard.one function parameter ⊓
      InternalOriginalUniformApplicationTyping.applicationPremises (readyData data window)
        arrow domain codomain function argument out parameter).imp
      (bottomGraph InternalOriginalStepGuard.one out).not))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomApplicationTargets
