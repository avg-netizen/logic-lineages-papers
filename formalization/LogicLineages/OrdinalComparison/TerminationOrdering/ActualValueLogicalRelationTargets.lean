module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualValueLogicalRelationDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualValueLogicalRelationTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts Source.SourceOpenedObservations Source.SourceArrowSuffixes FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment TypedObservationAccess RecursiveComparison ActualComparisonCompleteness ActualValueLogicalRelation

def BitClause : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (τ : Ty) (P : World I) (a : Value I τ P) (q : SyntaxAt I τ P),
  Related I above τ P a q → BitSound I above τ P a q

def FullTupleClause : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (τ : Ty) (P : World I) (a : Value I τ P) (q : SyntaxAt I τ P),
  Related I above τ P a q → ApplicationSound I τ (fun υ _ => Related I above υ) P a q

def DownwardClosure : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (τ : Ty) (P : World I) (a b : Value I τ P) (q : SyntaxAt I τ P),
  a ≤ b → Related I above τ P b q → Related I above τ P a q

def BottomRelated : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (τ : Ty) (P : World I) (q : SyntaxAt I τ P),
  Related I above τ P (ExecutableDomainBottom.bottomValue I τ P) q

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualValueLogicalRelationTargets
