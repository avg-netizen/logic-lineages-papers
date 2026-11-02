module
public import LogicLineages.OrdinalComparison.TerminationOrdering.LogicalRelationWorldsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ConstructorInputLogicalRelation
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice FunctionalSpineActions ActualValueLogicalRelation RecursiveComparison

def PackedRelated {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity)
    (above : Symbol → Symbol → Prop) (P : World I) (a : TypedExtraDownsets.Packed I P)
    (q : RecursiveComparison.Packed Symbol arity (portTypes P.val++I.context)) : Prop :=
  ∃ t : SyntaxAt I a.1.val P,q=⟨a.1.val,t⟩ ∧ Related I above a.1.val P a.2 t

def ExtrasRelated {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity)
    (above : Symbol → Symbol → Prop) (P : World I) (E : Extras I P) {types : List Ty}
    (qs : Arguments Symbol arity (portTypes P.val++I.context) types) : Prop :=
  ∀ a : TypedExtraDownsets.Packed I P,contains E a → ∃ q ∈ argumentList qs,PackedRelated I above P a q

def InputRelated {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity)
    (above : Symbol → Symbol → Prop) (f : HeadIndex I) (P : World I) (a : Inputs I f P)
    (base : Arguments Symbol arity (portTypes P.val++I.context) (headArguments arity f.val))
    {types : List Ty} (extras : Arguments Symbol arity (portTypes P.val++I.context) types) : Prop :=
  (∀ i,Related I above ((headArguments arity f.val).get i) P (a.1 i) (argumentAt base i)) ∧ ExtrasRelated I above P a.2 extras

def FamilySound {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity)
    (above : Symbol → Symbol → Prop) (M : Constructors I) : Prop :=
  ∀ (f : HeadIndex I) (τ : TypeIndex I) (P : World I) (a : Inputs I f P)
    (base : Arguments Symbol arity (portTypes P.val++I.context) (headArguments arity f.val))
    (types : List Ty) (extras : Arguments Symbol arity (portTypes P.val++I.context) types),
    InputRelated I above f P a base extras → Related I above τ.val P (M.val f τ P a) (.marked f.val τ.val base types extras)

end LogicLineages.OrdinalComparison.TerminationOrdering.ConstructorInputLogicalRelation
