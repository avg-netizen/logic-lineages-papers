module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RelatedOccurrenceMatchingProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.CopyStatStageSoundness
open Source Source.SourceMarkedSyntax Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice RecursiveComparison ConstructorInputLogicalRelation ActualComparisonCompleteness

/-- Literal marked source state, with every original extra occurrence retained. -/
def sourceState {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} (f : HeadIndex I) (τ : TypeIndex I)
    (P : World I) (base : Arguments Symbol arity (portTypes P.val++I.context) (headArguments arity f.val))
    (types : List Ty) (extras : Arguments Symbol arity (portTypes P.val++I.context) types) :=
  MarkedTerm.marked f.val τ.val base types extras

end LogicLineages.OrdinalComparison.TerminationOrdering.CopyStatStageSoundness
