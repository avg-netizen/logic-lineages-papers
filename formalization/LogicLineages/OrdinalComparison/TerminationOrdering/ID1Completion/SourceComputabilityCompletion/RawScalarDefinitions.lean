module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericCarrierDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.RawScalar
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Fixedness of the SAME original parameterized transition. There is no
requested-type coordinate and no extra type-domain convention. -/
def fixed (data : Data) : Program 2 :=
  InternalApplicationStepPeel.same
    (InternalParameterizedBoundedDescentNormalizer.transition data.oldRepresentative
      (InternalOriginalUniformDescentSelection.validity data)) (.projection 0)

/-- Raw canonical scalar carrier on [value,parameter], selected from the
same globally selected four-leaf Data as canonical typedness. -/
def checker (data : Data) : Program 2 :=
  InternalAcceptance.conjunction (InternalOriginalUniformDescentSelection.validity data) (fixed data)

def accepted {α : Type} (data : Data) (value parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 (checker data) InternalOriginalStepGuard.one value parameter

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.RawScalar
