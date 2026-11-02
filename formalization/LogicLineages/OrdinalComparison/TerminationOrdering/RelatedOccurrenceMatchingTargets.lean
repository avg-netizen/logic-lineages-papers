module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RelatedOccurrenceMatchingDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RelatedOccurrenceMatchingTargets
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits RecursiveComparison TypedExtraDownsets FiniteOccurrenceMatching ConstructorInputLogicalRelation ActualComparisonCompletenessSupportProof RelatedOccurrenceMatching

def PairSound : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (P : World I) (a : TypedExtraDownsets.Packed I P) (o : Observation Symbol arity I.context (budget I)) (s t : RecursiveComparison.Packed Symbol arity (portTypes P.val++I.context)),
  PackedRelated I above P a s → Observed I P o t →
  (pairBit false a o=true → Weak Symbol arity above (portTypes P.val++I.context) s t) ∧
  (pairBit true a o=true → Strict Symbol arity above (portTypes P.val++I.context) s t)

def WeakSound : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (P : World I) (values : List (TypedExtraDownsets.Packed I P)) (os : List (Observation Symbol arity I.context (budget I))) (ss ts : List (RecursiveComparison.Packed Symbol arity (portTypes P.val++I.context))),
  List.Forall₂ (PackedRelated I above P) values ss → List.Forall₂ (Observed I P) os ts → weakTest (pairBit false) values os=true →
  ∃ matched,ts.Perm matched ∧ WeakMatch Symbol arity above (portTypes P.val++I.context) ss matched

def StrictSound : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (P : World I) (values : List (TypedExtraDownsets.Packed I P)) (os : List (Observation Symbol arity I.context (budget I))) (ss ts : List (RecursiveComparison.Packed Symbol arity (portTypes P.val++I.context))),
  List.Forall₂ (PackedRelated I above P) values ss → List.Forall₂ (Observed I P) os ts → strictTest (pairBit false) (pairBit true) values os=true →
  StrictMultiset Symbol arity above (portTypes P.val++I.context) ss ts

end LogicLineages.OrdinalComparison.TerminationOrdering.RelatedOccurrenceMatchingTargets
