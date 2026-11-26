module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonapplicationChecker
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors

/-- Negation of the literal original raw constructor-tag graph at two.
The numeric two is the existing positionTerm, not a decoded source predicate.
No typing, validity, certificate well-formedness or native parse is assumed. -/
def nonapplicationRoot {α : Type} (source : OTerm α) : Formula α :=
  (graph1 (InternalApplicationStepPeel.constructorTag (.projection 0))
    positionTerm source).not

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonapplicationChecker
