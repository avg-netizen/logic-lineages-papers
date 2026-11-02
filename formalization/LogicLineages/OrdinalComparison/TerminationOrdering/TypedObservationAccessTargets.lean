module
public import LogicLineages.OrdinalComparison.TerminationOrdering.TypedObservationAccessDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.TypedObservationAccessTargets
open Source Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains ExecutableDomainBottom TypedObservationAccess

def TrueCalibration : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (τ : Ty) (P : World I) (strict : Bool) (a : Value I τ P) (o : Observation Symbol arity I.context (budget I)), readBit strict a o=true ↔ ∃ h : Accepted I τ P o,acceptedCoordinate strict a o h=true

def RejectedFalse : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (τ : Ty) (P : World I) (strict : Bool) (a : Value I τ P) (o : Observation Symbol arity I.context (budget I)), ¬Accepted I τ P o → readBit strict a o=false

def TypedCoordinate : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (τ : Ty) (P : World I) (strict : Bool) (a : Value I τ P) (Q : Future P) (o : ObservationAt I τ Q.val), readBit strict a o.val=coordinate strict a Q o

def ReadMonotone : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (τ : Ty) (P : World I) (strict : Bool) (a b : Value I τ P) (o : Observation Symbol arity I.context (budget I)), a ≤ b → readBit strict a o ≤ readBit strict b o

def RestrictionAccess : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (τ : Ty) (P : World I) (strict : Bool) (Q : World I) (h : Extends P Q) (a : Value I τ P) (o : Observation Symbol arity I.context (budget I)), (∀ p ∈ Q.val,p ∈ o.ports) → readBit strict (RecursiveNaturalDomains.weaken h a) o=readBit strict a o

def BottomFalse : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (τ : Ty) (P : World I) (strict : Bool) (o : Observation Symbol arity I.context (budget I)), readBit strict (bottomValue I τ P) o=false

end LogicLineages.OrdinalComparison.TerminationOrdering.TypedObservationAccessTargets
