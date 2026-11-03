module
public import LogicLineages.OrdinalComparison.TerminationOrdering.LambdaObservationMatchingDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.LambdaObservationMatchingTargets
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment MarkedFAbsTest TypedObservationAccess LambdaObservationMatching

def OriginalBodyDecrease : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (σ υ : Ty) (body : MarkedTerm Symbol arity (σ::Γ) υ) , sizeOf body < sizeOf (MarkedTerm.lam body)

def OpeningEnvironment : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (P : World I) (ρ : Environment I Γ P) (σ υ : Ty) (i : Fin (budget I)) (h : Opening I P σ υ i), openingEnvironment ρ σ υ i h Variable.here = LiteralVariableValueProof.variableValue (I := I) (P := ⟨(i,σ)::P.val,h.2.1⟩) Variable.here ∧ ∀ {τ} (v : Variable Γ τ),openingEnvironment ρ σ υ i h (Variable.there v)=RecursiveNaturalDomains.weaken (fun p hp => List.mem_cons_of_mem _ hp) (ρ v)

def GenuineFreshOpening : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (P : World I) (σ υ : Ty) (body : Term Symbol arity (σ::(portTypes P.val++I.context)) υ), (⟨P.val,.arrow σ υ,.lam body⟩ : Observation Symbol arity I.context (budget I)) ∈ observations (budget I) I.target → ∃ (i : Fin (budget I)) (h : Opening I P σ υ i), (⟨(i,σ)::P.val,υ,body⟩ : Observation Symbol arity I.context (budget I)) ∈ observations (budget I) I.target

def LiteralMatch : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (σ υ : Ty) (body : MarkedTerm Symbol arity (σ::Γ) υ) (E : BodyEvaluator I body) (P : World I) (ρ : Environment I Γ P) (strict : Bool) (targetBody : Term Symbol arity (σ::(portTypes P.val++I.context)) υ), matchTerm strict E ρ (.lam targetBody)=true ↔ ∃ (i : Fin (budget I)) (h : Opening I P σ υ i),openedRead strict E ρ targetBody i h=true

def BitsMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (σ υ : Ty) (body : MarkedTerm Symbol arity (σ::Γ) υ) (E F : BodyEvaluator I body) (P : World I) (ρ η : Environment I Γ P), EvaluatorsLE E F → EnvLE ρ η → lambdaBits E ρ ≤ lambdaBits F η

def BitsRestriction : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (σ υ : Ty) (body : MarkedTerm Symbol arity (σ::Γ) υ) (E : BodyEvaluator I body) (P Q : World I) (h : Extends P Q) (ρ : Environment I Γ P), FiniteObservationBits.weaken h (lambdaBits E ρ)=lambdaBits E (restrict h ρ)

end LogicLineages.OrdinalComparison.TerminationOrdering.LambdaObservationMatchingTargets
