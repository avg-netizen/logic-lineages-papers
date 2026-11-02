module
public import LogicLineages.OrdinalComparison.TerminationOrdering.LiteralVariableValueProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.TypedObservationAccess
open Source Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains ExecutableDomainBottom

def Accepted {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) (τ : Ty) (P : World I)
    (o : Observation Symbol arity I.context (budget I)) : Prop :=
  o.ports ∈ worldList I ∧ (∀ p ∈ P.val,p ∈ o.ports) ∧ o.resultType=τ ∧ o ∈ observations (budget I) I.target

instance acceptedDecision {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity)
    (τ : Ty) (P : World I) (o : Observation Symbol arity I.context (budget I)) : Decidable (Accepted I τ P o) :=
  inferInstanceAs (Decidable (o.ports ∈ worldList I ∧ (∀ p ∈ P.val,p ∈ o.ports) ∧ o.resultType=τ ∧ o ∈ observations (budget I) I.target))

def coordinate {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {τ : Ty} {P : World I}
    (strict : Bool) (a : Value I τ P) (Q : Future P) (o : ObservationAt I τ Q.val) : Bool :=
  if strict then ((layerView I τ P a).val.1 Q).2.2 o else ((layerView I τ P a).val.1 Q).2.1 o

def acceptedCoordinate {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {τ : Ty} {P : World I}
    (strict : Bool) (a : Value I τ P) (o : Observation Symbol arity I.context (budget I)) (h : Accepted I τ P o) : Bool :=
  coordinate strict a ⟨⟨o.ports,h.1⟩,h.2.1⟩ ⟨o,h.2.2.2,rfl,h.2.2.1⟩

/-- Total actual-observation access: every failed type, world, extension or membership guard returns false. -/
def readBit {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity} {τ : Ty} {P : World I}
    (strict : Bool) (a : Value I τ P) (o : Observation Symbol arity I.context (budget I)) : Bool :=
  if h : Accepted I τ P o then acceptedCoordinate strict a o h else false

end LogicLineages.OrdinalComparison.TerminationOrdering.TypedObservationAccess
