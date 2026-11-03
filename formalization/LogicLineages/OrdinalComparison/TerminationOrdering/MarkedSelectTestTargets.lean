module
public import LogicLineages.OrdinalComparison.TerminationOrdering.MarkedSelectTestDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.MarkedSelectTestTargets
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice TypedObservationAccess OrdinaryFunctionalValue FullTuplePacking MarkedCopyTest MarkedSelectTest

def SelfTupleCalibration : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M : Constructors I) (f : HeadIndex I) (P : World I) (a : Inputs I f P) (τ : TypeIndex I) (s : Suffix τ.val), (∀ i,selfTuple M f a τ s i=M.val f (argumentTag I τ s i) P a) ∧ (packTuple τ s (selfTuple M f a τ s)).length=s.val.1.length

def SelectCalibration : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M : Constructors I) (f : HeadIndex I) (P : World I) (a : Inputs I f P) (o : Observation Symbol arity I.context (budget I)), selectTest M f a o=true ↔ ∃ p : Packed I P,(p ∈ packBase f a.1 ∨ contains a.2 p) ∧ ((p.1.val=o.resultType ∧ readBit false p.2 o=true) ∨ ∃ s : Suffix p.1.val,s.val.2=o.resultType ∧ readBit false (applyValue p.2 s (selfTuple M f a p.1 s)) o=true)

def SelectedMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (f : HeadIndex I) (P : World I) (a b : Inputs I f P), a ≤ b → ∀ p,Selected f a p → ∃ q,Selected f b q ∧ PackedLE p q

def TestMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M N : Constructors I) (f : HeadIndex I) (P : World I) (a b : Inputs I f P) (o : Observation Symbol arity I.context (budget I)), M ≤ N → a ≤ b → selectTest M f a o ≤ selectTest N f b o

def CoordinatesMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M N : Constructors I) (f : HeadIndex I) (τ : Ty) (P : World I) (a b : Inputs I f P), M ≤ N → a ≤ b → selectCoordinates M f τ a ≤ selectCoordinates N f τ b

def CoordinatesWeakening : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M : Constructors I) (f : HeadIndex I) (τ : Ty) (P Q : World I) (h : Extends P Q) (a : Inputs I f P), project h (selectCoordinates M f τ a)=selectCoordinates M f τ ((inputFamily I f).restrict h a)

end LogicLineages.OrdinalComparison.TerminationOrdering.MarkedSelectTestTargets
