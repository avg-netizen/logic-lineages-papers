module
public import LogicLineages.OrdinalComparison.TerminationOrdering.MarkedFAbsTestDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.MarkedFAbsTestTargets
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice TypedObservationAccess MarkedCopyTest MarkedFAbsTest

def FreshAvailability : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (P : World I) (σ υ : Ty) (body : Term Symbol arity (σ::(portTypes P.val++I.context)) υ), (⟨P.val,.arrow σ υ,.lam body⟩ : Observation Symbol arity I.context (budget I)) ∈ observations (budget I) I.target → ∃ i : Fin (budget I),i ∉ P.val.map Prod.fst

def GenuineOpeningGuards : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (P : World I) (σ υ : Ty) (body : Term Symbol arity (σ::(portTypes P.val++I.context)) υ) (i : Fin (budget I)), (⟨P.val,.arrow σ υ,.lam body⟩ : Observation Symbol arity I.context (budget I)) ∈ observations (budget I) I.target → i ∉ P.val.map Prod.fst → Opening I P σ υ i ∧ (⟨(i,σ)::P.val,υ,body⟩ : Observation Symbol arity I.context (budget I)) ∈ observations (budget I) I.target

def LambdaCalibration : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M : Constructors I) (f : HeadIndex I) (P : World I) (σ υ : Ty) (body : Term Symbol arity (σ::(portTypes P.val++I.context)) υ) (a : Inputs I f P), lambdaTest M f a σ υ body=true ↔ ∃ i : Fin (budget I),∃ h : Opening I P σ υ i,openingRead M f a σ υ body i h=true

def LiteralLambdaEquation : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M : Constructors I) (f : HeadIndex I) (P : World I) (σ υ : Ty) (body : Term Symbol arity (σ::(portTypes P.val++I.context)) υ) (a : Inputs I f P), fAbsTest M f a ⟨P.val,.arrow σ υ,.lam body⟩=lambdaTest M f a σ υ body

def TestMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M N : Constructors I) (f : HeadIndex I) (P : World I) (a b : Inputs I f P) (o : Observation Symbol arity I.context (budget I)), M ≤ N → a ≤ b → fAbsTest M f a o ≤ fAbsTest N f b o

def CoordinatesMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M N : Constructors I) (f : HeadIndex I) (τ : Ty) (P : World I) (a b : Inputs I f P), M ≤ N → a ≤ b → fAbsCoordinates M f τ a ≤ fAbsCoordinates N f τ b

def CoordinatesWeakening : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M : Constructors I) (f : HeadIndex I) (τ : Ty) (P Q : World I) (h : Extends P Q) (a : Inputs I f P), project h (fAbsCoordinates M f τ a)=fAbsCoordinates M f τ ((inputFamily I f).restrict h a)

end LogicLineages.OrdinalComparison.TerminationOrdering.MarkedFAbsTestTargets
