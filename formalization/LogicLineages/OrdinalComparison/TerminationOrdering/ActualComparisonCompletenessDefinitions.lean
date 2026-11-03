module
public import LogicLineages.OrdinalComparison.TerminationOrdering.LiteralWorldTransportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualComparisonCompleteness
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment CoherentConstructorLattice ConfinedStructuralInterpretation TypedObservationAccess RecursiveComparison SourceConstructorIteration

def observedTerm {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} {P : World I} {τ : Ty}
    (o : ObservationAt I τ P) : MarkedTerm Symbol arity (portTypes P.val++I.context) τ :=
  embed (LambdaObservationMatching.observationBody o)

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualComparisonCompleteness
