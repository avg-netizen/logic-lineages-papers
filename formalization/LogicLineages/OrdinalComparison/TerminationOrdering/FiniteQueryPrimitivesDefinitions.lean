module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ComparisonFreeVariablesDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.TypeClosureDefinitions
public import LogicLineages.OrdinalComparison.SourceOpenedObservationsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FiniteQueryPrimitives
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open Source.SourceTypeSupport Source.SourceFreeOccurrences Source.SourcePortContexts Source.SourceOpenedObservations
open RecursiveComparison ComparisonFreeVariables

mutual
def markedHeads {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) : List (Head Symbol) :=
  match q with
  | .var _ => []
  | .lam body => markedHeads body
  | .ordinary h base => h::argumentHeads base
  | .marked h _ base _ extras => h::(argumentHeads base++argumentHeads extras)
def argumentHeads {Symbol : Type} {arity : Symbol → Nat} {Γ types : List Ty}
    (args : Arguments Symbol arity Γ types) : List (Head Symbol) :=
  match args with
  | .nil => []
  | .cons q rest => markedHeads q++argumentHeads rest
end

def liftAllowedList {Γ : List Ty} (a : Allowed Γ) : (Θ : List Ty) → Allowed (Θ++Γ)
  | [] => a
  | σ::Θ => liftAllowed (liftAllowedList a Θ)

structure Query (Symbol : Type) (arity : Symbol → Nat) (Γ : List Ty) (B : Nat) where
  observation : Observation Symbol arity Γ B
  source : Packed Symbol arity (portTypes observation.ports++Γ)

def inputTypes {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {σ τ : Ty}
    (s : Term Symbol arity Γ σ) (t : Term Symbol arity Γ τ) : Finset Ty := typeSupport s ∪ typeSupport t

def inputNames {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {σ τ : Ty}
    (s : Term Symbol arity Γ σ) (t : Term Symbol arity Γ τ) : Allowed Γ :=
  fun {υ} v => (⟨υ,v⟩ : PackedVariable Γ) ∈ freeOccurrences s++freeOccurrences t

def initial {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {σ τ : Ty}
    (s : Term Symbol arity Γ σ) (t : Term Symbol arity Γ τ) : Query Symbol arity Γ (lambdaDepth t) :=
  ⟨⟨[],τ,t⟩,⟨σ,embed s⟩⟩

def Frame {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {σ τ : Ty}
    (s : Term Symbol arity Γ σ) (t : Term Symbol arity Γ τ) (q : Query Symbol arity Γ (lambdaDepth t)) : Prop :=
  typesAllowed (fun υ => υ ∈ inputTypes s t) q.source.2 ∧
  headsAllowed (fun h => h ∈ markedHeads (embed s)) q.source.2 ∧
  Supported q.source.2 (liftAllowedList (inputNames s t) (portTypes q.observation.ports)) ∧
  q.observation ∈ observations (lambdaDepth t) t

structure SelectAttempt {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Γ (headArguments arity f))
    (extraTypes : List Ty) (extras : Arguments Symbol arity Γ extraTypes) (τ : Ty) where
  selectedType : Ty
  selected : MarkedTerm Symbol arity Γ selectedType
  suppliedTypes : List Ty
  suffix : selectedType=arrows suppliedTypes τ
  selectedMember : (⟨selectedType,selected⟩ : Packed Symbol arity Γ) ∈ argumentList base++argumentList extras

def attemptArguments {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty}
    {f : Head Symbol} {base : Arguments Symbol arity Γ (headArguments arity f)}
    {extraTypes : List Ty} {extras : Arguments Symbol arity Γ extraTypes} {τ : Ty}
    (r : SelectAttempt f base extraTypes extras τ) : Arguments Symbol arity Γ r.suppliedTypes :=
  selfArguments f base extraTypes extras r.suppliedTypes

def attemptResult {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty}
    {f : Head Symbol} {base : Arguments Symbol arity Γ (headArguments arity f)}
    {extraTypes : List Ty} {extras : Arguments Symbol arity Γ extraTypes} {τ : Ty}
    (r : SelectAttempt f base extraTypes extras τ) : Option (MarkedTerm Symbol arity Γ τ) :=
  applyOriginalWith r.selected (fun v => .var v) (attemptArguments r) r.suffix

end LogicLineages.OrdinalComparison.TerminationOrdering.FiniteQueryPrimitives
