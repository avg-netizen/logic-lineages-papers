module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FiniteOccurrenceMatchingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.GuardedQueryGraphSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryObservationView
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer

abbrev RootData (Symbol : Type) (arity : Symbol → Nat) (Γ : List Ty) :=
  Σ f : Head Symbol,Arguments Symbol arity Γ (headArguments arity f)

def packedView {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty}
    (p : RecursiveComparison.Packed Symbol arity Γ) : Option (RootData Symbol arity Γ) :=
  match p with
  | ⟨_,.ordinary f base⟩ => some ⟨f,base⟩
  | _ => none

def rootView {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (t : Term Symbol arity Γ τ) : Option (RootData Symbol arity Γ) := packedView ⟨τ,embed t⟩

/-- Literal original immediate arguments: an application contributes exactly function and argument. -/
def childTerms {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (t : Term Symbol arity Γ τ) : List (Σ υ,Term Symbol arity Γ υ) :=
  match t with
  | .app f a => [⟨_,f⟩,⟨_,a⟩]
  | .ranked s args => List.ofFn fun i => ⟨.ground,args i⟩
  | _ => []

def embedChild {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty}
    (p : Σ υ,Term Symbol arity Γ υ) : RecursiveComparison.Packed Symbol arity Γ := ⟨p.1,embed p.2⟩

def observeChild {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {B : Nat}
    (P : PortContext B) (p : Σ υ,Term Symbol arity (portTypes P++Γ) υ) : Observation Symbol arity Γ B := ⟨P,p.1,p.2⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryObservationView
