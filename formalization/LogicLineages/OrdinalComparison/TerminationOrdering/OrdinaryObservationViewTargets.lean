module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryObservationViewDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryObservationViewTargets
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer OrdinaryObservationView

def RootCalibration : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ : List Ty) (τ : Ty) (t : Term Symbol arity Γ τ) (f : Head Symbol) (base : Arguments Symbol arity Γ (headArguments arity f)), rootView t=some ⟨f,base⟩ ↔ (⟨τ,embed t⟩ : RecursiveComparison.Packed Symbol arity Γ)=⟨headResult f,.ordinary f base⟩

def ArgumentCalibration : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ : List Ty) (τ : Ty) (t : Term Symbol arity Γ τ) (f : Head Symbol) (base : Arguments Symbol arity Γ (headArguments arity f)), rootView t=some ⟨f,base⟩ → (childTerms t).map embedChild=RecursiveComparison.argumentList base

def ArgumentTypeCalibration : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ : List Ty) (τ : Ty) (t : Term Symbol arity Γ τ) (f : Head Symbol) (base : Arguments Symbol arity Γ (headArguments arity f)), rootView t=some ⟨f,base⟩ → (childTerms t).map Sigma.fst=headArguments arity f

def PlainChildrenCalibration : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ : List Ty) (B : Nat) (o : Observation Symbol arity Γ B), (childTerms o.body).map (observeChild o.ports)=plainChildren o

def ChildProvenance : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (I : Input Symbol arity) (o c : Observation Symbol arity I.context (budget I)), o ∈ observations (budget I) I.target → c ∈ (childTerms o.body).map (observeChild o.ports) → c ∈ observations (budget I) I.target ∧ c.ports=o.ports ∧ c.resultType ∈ TypedExtraDownsets.types I

def DeclaredArgumentTypes : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (I : Input Symbol arity) (o : Observation Symbol arity I.context (budget I)) (f : Head Symbol) (base : Arguments Symbol arity (portTypes o.ports++I.context) (headArguments arity f)), o ∈ observations (budget I) I.target → rootView o.body=some ⟨f,base⟩ → ∀ υ ∈ headArguments arity f,υ ∈ TypedExtraDownsets.types I

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryObservationViewTargets
