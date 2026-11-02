module
public import LogicLineages.OrdinalComparison.SourceOpenedObservationsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceObservationCoding
open Source Source.SourceTypedPorts Source.SourcePortContexts Source.SourceOpenedObservations

/-- Literal constructor tree, with application-domain and binder types retained. -/
inductive Code (Symbol : Type) where
  | var (index : Nat)
  | app (domain : Ty) (function argument : Code Symbol)
  | lam (domain : Ty) (body : Code Symbol)
  | zero
  | succ
  | cases (result : Ty)
  | recursor (result : Ty)
  | ranked (symbol : Symbol) (arguments : Code Symbol)
  | argumentsNil
  | argumentsCons (head tail : Code Symbol)
  deriving DecidableEq

def argumentCodes {Symbol : Type} : List (Code Symbol) → Code Symbol
  | [] => .argumentsNil
  | h::t => .argumentsCons h (argumentCodes t)

def termCode {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty} :
    Term Symbol arity Γ τ → Code Symbol
  | .var v => .var (variableIndex v)
  | @Term.app _ _ _ σ _ f a => .app σ (termCode f) (termCode a)
  | @Term.lam _ _ _ σ _ body => .lam σ (termCode body)
  | .zeroC => .zero
  | .succC => .succ
  | .caseC υ => .cases υ
  | .recC υ => .recursor υ
  | .ranked hd args => .ranked hd (argumentCodes (List.ofFn fun i => termCode (args i)))

abbrev ObservationCode (Symbol : Type) (B : Nat) := PortContext B × Ty × Code Symbol

def observationCode {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {B : Nat}
    (o : Observation Symbol arity Γ B) : ObservationCode Symbol B :=
  (o.ports,o.resultType,termCode o.body)

def termEqual {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (s t : Term Symbol arity Γ τ) : Bool := decide (termCode s=termCode t)

def observationEqual {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {Γ : List Ty} {B : Nat}
    (o p : Observation Symbol arity Γ B) : Bool := decide (observationCode o=observationCode p)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceObservationCoding
