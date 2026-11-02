module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ConstructorInputLogicalRelationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RelatedOccurrenceMatching
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits RecursiveComparison TypedExtraDownsets FiniteOccurrenceMatching ConstructorInputLogicalRelation ActualComparisonCompletenessSupportProof

def Observed {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) (P : World I)
    (o : Observation Symbol arity I.context (budget I)) (q : RecursiveComparison.Packed Symbol arity (portTypes P.val++I.context)) : Prop :=
  ∃ ho : o ∈ observations (budget I) I.target,∃ hp : o.ports=P.val,q=decode o hp

end LogicLineages.OrdinalComparison.TerminationOrdering.RelatedOccurrenceMatching
