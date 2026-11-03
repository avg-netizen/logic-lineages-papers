module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ConstructorInputLogicalRelationDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ConstructorInputLogicalRelationTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice FunctionalSpineActions ActualValueLogicalRelation RecursiveComparison ConstructorInputLogicalRelation

def PackedDownward : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (P : World I) (a b : TypedExtraDownsets.Packed I P) (q : RecursiveComparison.Packed Symbol arity (portTypes P.val++I.context)),
  PackedLE a b → PackedRelated I above P b q → PackedRelated I above P a q

def InputAppend : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (f : HeadIndex I) (P : World I) (a : Inputs I f P)
  (base : Arguments Symbol arity (portTypes P.val++I.context) (headArguments arity f.val))
  (types : List Ty) (extras : Arguments Symbol arity (portTypes P.val++I.context) types)
  (more : List Ty) (ht : ∀ τ ∈ more,τ ∈ TypedExtraDownsets.types I)
  (values : FullListValueApplication.Values I more P) (args : Arguments Symbol arity (portTypes P.val++I.context) more),
  InputRelated I above f P a base extras → (∀ i,Related I above (more.get i) P (values i) (argumentAt args i)) →
  InputRelated I above f P (FunctionalTupleBuilder.appendInput a (packArguments more ht values)) base (appendArguments extras args)

def InputWeakening : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (f : HeadIndex I) (P Q : World I) (h : Extends P Q) (a : Inputs I f P)
  (base : Arguments Symbol arity (portTypes P.val++I.context) (headArguments arity f.val))
  (types : List Ty) (extras : Arguments Symbol arity (portTypes P.val++I.context) types),
  InputRelated I above f P a base extras → InputRelated I above f Q ((inputFamily I f).restrict h a)
    (renameArguments base (LogicalRelationWorlds.portRename h)) (renameArguments extras (LogicalRelationWorlds.portRename h))

def BottomFamilySound : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop), FamilySound I above (SourceConstructorIteration.bottomConstructors I)

def FamilyDownward : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (M N : Constructors I),M ≤ N → FamilySound I above N → FamilySound I above M

end LogicLineages.OrdinalComparison.TerminationOrdering.ConstructorInputLogicalRelationTargets
