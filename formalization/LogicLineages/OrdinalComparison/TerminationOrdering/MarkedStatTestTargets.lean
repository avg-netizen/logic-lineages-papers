module
public import LogicLineages.OrdinalComparison.TerminationOrdering.MarkedStatTestDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.MarkedStatTestTargets
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice TypedObservationAccess OrdinaryObservationView OrdinaryFunctionalValue FiniteOccurrenceMatching MarkedCopyTest MarkedStatTest

def StrictSourceMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (P : World I) (xs ys : List (Packed I P)) (ts : List (Observation Symbol arity I.context (budget I))), List.Forall₂ PackedLE xs ys → strictTest (pairBit false) (pairBit true) xs ts ≤ strictTest (pairBit false) (pairBit true) ys ts

def StatCalibration : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M : Constructors I) (f : HeadIndex I) (P : World I) (a : Inputs I f P) (o : Observation Symbol arity I.context (budget I)), statTest M f a o=true ↔ ∃ (g : Head Symbol) (args : Arguments Symbol arity (portTypes o.ports++I.context) (headArguments arity g)),rootView o.body=some ⟨g,args⟩ ∧ RecursiveComparison.headEquivalent f.val g ∧ (∃ kept removed retained inserted,(packBase f a.1).Perm (kept++removed) ∧ (plainChildren o).Perm (retained++inserted) ∧ removed≠[] ∧ List.Forall₂ (fun s t => pairBit false s t=true) kept retained ∧ (∀ t ∈ inserted,∃ s ∈ removed,pairBit true s t=true)) ∧ (∀ c ∈ plainChildren o,∃ ht : c.resultType ∈ types I,readBit false (M.val f ⟨c.resultType,ht⟩ P a) c=true)

def TestMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M N : Constructors I) (f : HeadIndex I) (P : World I) (a b : Inputs I f P) (o : Observation Symbol arity I.context (budget I)), M ≤ N → a ≤ b → statTest M f a o ≤ statTest N f b o

def CoordinatesMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M N : Constructors I) (f : HeadIndex I) (τ : Ty) (P : World I) (a b : Inputs I f P), M ≤ N → a ≤ b → statCoordinates M f τ a ≤ statCoordinates N f τ b

def CoordinatesWeakening : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M : Constructors I) (f : HeadIndex I) (τ : Ty) (P Q : World I) (h : Extends P Q) (a : Inputs I f P), project h (statCoordinates M f τ a)=statCoordinates M f τ ((inputFamily I f).restrict h a)

end LogicLineages.OrdinalComparison.TerminationOrdering.MarkedStatTestTargets
