module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomParameterDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSource
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open SourceComputabilityFormulaSupportProof
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- One global Data: bottom-context normalization first, representative
shape guard second, the existing membership normalization exactly once. -/
def selection (data : Data) (window : Program 1) : Data :=
  BottomRepresentative.readyData (BottomParameter.baseData data) window

def bottomNumber (tau : Ty) : Nat :=
  Nat.pair (NumberedLeastCodeRepresentative.typeNumber tau)
    (Nat.pair 3 (NumberedLeastCodeRepresentative.typeNumber tau))

def bottomTerm {α : Type} (tau : Ty) : OrdinaryArithmetic.Term α :=
  numeral (bottomNumber tau)

def typedBottom {α : Type} (data : Data) (window : Program 1)
    (tau : Ty) (parameter : OrdinaryArithmetic.Term α) : Formula α :=
  let selected := selection data window
  InternalOriginalUniformDescentSelection.typedAccepted selected.oldRepresentative
    (InternalOriginalUniformDescentSelection.validity selected) selected.member
    (bottomTerm tau) (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) parameter

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSource
