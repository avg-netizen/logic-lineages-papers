module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FiniteQueryPrimitivesDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OriginalApplicationTrace
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open ComparisonFreeVariables FiniteQueryPrimitives

structure Configuration (Symbol : Type) (arity : Symbol → Nat) (Δ : List Ty) (τ : Ty) where
  sourceContext : List Ty
  sourceType : Ty
  suppliedTypes : List Ty
  source : MarkedTerm Symbol arity sourceContext sourceType
  environment : MarkedSubstitution Symbol arity sourceContext Δ
  arguments : Arguments Symbol arity Δ suppliedTypes
  suffix : sourceType=arrows suppliedTypes τ

def evaluate {Symbol : Type} {arity : Symbol → Nat} {Δ : List Ty} {τ : Ty}
    (c : Configuration Symbol arity Δ τ) : Option (MarkedTerm Symbol arity Δ τ) :=
  applyOriginalWith c.source c.environment c.arguments c.suffix

def next {Symbol : Type} {arity : Symbol → Nat} {Δ : List Ty} {τ : Ty}
    (c : Configuration Symbol arity Δ τ) : Option (Configuration Symbol arity Δ τ) :=
  match c with
  | ⟨Γ,_,_,q,env,args,suffix⟩ => match q with
    | .lam body => match args with
      | .nil => none
      | .cons a rest => some ⟨_,_,_,body,extendEnvironment env (transportTerm (Ty.arrow.inj suffix).1.symm a),rest,(Ty.arrow.inj suffix).2⟩
    | .var _ | .ordinary _ _ | .marked _ _ _ _ _ => none

def terminal {Symbol : Type} {arity : Symbol → Nat} {Δ : List Ty} {τ : Ty}
    (c : Configuration Symbol arity Δ τ) : Option (MarkedTerm Symbol arity Δ τ) :=
  match c with
  | ⟨Γ,_,_,q,env,args,suffix⟩ => match q with
    | .var v => match args with
      | .nil => some (transportTerm suffix (env v))
      | .cons _ _ => none
    | .lam body => match args with
      | .nil => some (transportTerm suffix (substituteTerm (.lam body) env))
      | .cons _ _ => none
    | .ordinary f base => match args with
      | .nil => some (transportTerm suffix (substituteTerm (.ordinary f base) env))
      | .cons a rest => some (.marked f τ (substituteArguments base env) _ (.cons a rest))
    | .marked f out base types extras => match args with
      | .nil => some (transportTerm suffix (substituteTerm (.marked f out base types extras) env))
      | .cons a rest => some (.marked f τ (substituteArguments base env) _ (appendArguments (substituteArguments extras env) (.cons a rest)))

inductive Execution {Symbol : Type} {arity : Symbol → Nat} {Δ : List Ty} {τ : Ty} :
    Configuration Symbol arity Δ τ → Configuration Symbol arity Δ τ → Prop where
  | refl (c) : Execution c c
  | step {c d e} : next c=some d → Execution d e → Execution c e

def Frame {Symbol : Type} {arity : Symbol → Nat} {Δ : List Ty} {τ : Ty}
    (K : Ty → Prop) (P : Head Symbol → Prop) (a : Allowed Δ) (c : Configuration Symbol arity Δ τ) : Prop :=
  typesAllowed K c.source ∧ substitutionTypesAllowed K c.environment ∧ argumentTypesAllowed K c.arguments ∧
  headsAllowed P c.source ∧ substitutionAllowed P c.environment ∧ argumentsAllowed P c.arguments ∧
  Supported c.source (fun v => Supported (c.environment v) a) ∧ ArgumentsSupported c.arguments a

def substitutedPayload {Symbol : Type} {arity : Symbol → Nat} {Δ : List Ty} {τ : Ty}
    (c : Configuration Symbol arity Δ τ) : MarkedTerm Symbol arity Δ c.sourceType := substituteTerm c.source c.environment

def appendedPayload {Symbol : Type} {arity : Symbol → Nat} {Δ : List Ty} {τ : Ty}
    (c : Configuration Symbol arity Δ τ) : Σ types,Arguments Symbol arity Δ types :=
  match c with
  | ⟨Γ,_,types,q,env,args,suffix⟩ => match q with
    | .marked _ _ _ extrasTypes extras => ⟨extrasTypes++types,appendArguments (substituteArguments extras env) args⟩
    | .var _ | .lam _ | .ordinary _ _ => ⟨types,args⟩

def PayloadBounds {Symbol : Type} {arity : Symbol → Nat} {Δ : List Ty} {τ : Ty}
    (K : Ty → Prop) (P : Head Symbol → Prop) (a : Allowed Δ) (c : Configuration Symbol arity Δ τ) : Prop :=
  K c.sourceType ∧ (∀ υ ∈ c.suppliedTypes,K υ) ∧ K τ ∧
  typesAllowed K (substitutedPayload c) ∧ headsAllowed P (substitutedPayload c) ∧ Supported (substitutedPayload c) a ∧
  argumentTypesAllowed K (appendedPayload c).2 ∧ argumentsAllowed P (appendedPayload c).2 ∧ ArgumentsSupported (appendedPayload c).2 a ∧
  ∀ r,evaluate c=some r → typesAllowed K r ∧ headsAllowed P r ∧ Supported r a

def ofSelect {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty}
    {f : Head Symbol} {base : Arguments Symbol arity Γ (headArguments arity f)}
    {extraTypes : List Ty} {extras : Arguments Symbol arity Γ extraTypes} {τ : Ty}
    (request : SelectAttempt f base extraTypes extras τ) : Configuration Symbol arity Γ τ :=
  ⟨Γ,request.selectedType,request.suppliedTypes,request.selected,(fun v => .var v),attemptArguments request,request.suffix⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.OriginalApplicationTrace
