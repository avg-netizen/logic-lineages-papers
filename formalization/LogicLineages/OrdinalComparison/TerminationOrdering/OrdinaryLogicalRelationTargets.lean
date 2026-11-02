module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualConstructorFamilySoundnessProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryLogicalRelationTargets
open Source Source.SourceMarkedSyntax Source.SourcePortContexts FiniteObservationBits CoherentConstructorLattice ConstructorInputLogicalRelation ActualValueLogicalRelation OrdinaryFunctionalValue SourceConstructorIteration

def OrdinaryRelated : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (M : Constructors I) (f : HeadIndex I) (P : World I) (b : BaseTuple I f P) (base : Arguments Symbol arity (portTypes P.val++I.context) (headArguments arity f.val)),
  FamilySound I above M → (∀ i,Related I above ((headArguments arity f.val).get i) P (b i) (argumentAt base i)) → Related I above (headResult f.val) P (ordinaryValue M f b) (.ordinary f.val base)

def ActualLimitOrdinaryRelated : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (f : HeadIndex I) (P : World I) (b : BaseTuple I f P) (base : Arguments Symbol arity (portTypes P.val++I.context) (headArguments arity f.val)),
  (∀ i,Related I above ((headArguments arity f.val).get i) P (b i) (argumentAt base i)) → Related I above (headResult f.val) P (ordinaryValue (limit I above) f b) (.ordinary f.val base)

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryLogicalRelationTargets
