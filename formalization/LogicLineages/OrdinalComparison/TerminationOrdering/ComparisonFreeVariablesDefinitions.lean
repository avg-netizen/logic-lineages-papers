module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveComparisonDefinitions
public import LogicLineages.OrdinalComparison.SourceFreeOccurrencesDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ComparisonFreeVariables
open Source Source.SourceMarkedSyntax Source.SourceFreeOccurrences

mutual
def markedOccurrences {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) : List (PackedVariable Γ) :=
  match q with
  | .var v => [⟨_,v⟩]
  | .lam body => (markedOccurrences body).filterMap dropBound
  | .ordinary _ args => argumentOccurrences args
  | .marked _ _ base _ extras => argumentOccurrences base++argumentOccurrences extras
def argumentOccurrences {Symbol : Type} {arity : Symbol → Nat} {Γ types : List Ty}
    (args : Arguments Symbol arity Γ types) : List (PackedVariable Γ) :=
  match args with
  | .nil => []
  | .cons q rest => markedOccurrences q++argumentOccurrences rest
end

abbrev Allowed (Γ : List Ty) := ∀ {σ : Ty}, Variable Γ σ → Prop

def liftAllowed {Γ : List Ty} {σ : Ty} (a : Allowed Γ) : Allowed (σ::Γ)
  | _,.here => True
  | _,.there v => a v

mutual
def Supported {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) (a : Allowed Γ) : Prop :=
  match q with
  | .var v => a v
  | .lam body => Supported body (liftAllowed a)
  | .ordinary _ base => ArgumentsSupported base a
  | .marked _ _ base _ extras => ArgumentsSupported base a ∧ ArgumentsSupported extras a
def ArgumentsSupported {Symbol : Type} {arity : Symbol → Nat} {Γ types : List Ty}
    (args : Arguments Symbol arity Γ types) (a : Allowed Γ) : Prop :=
  match args with
  | .nil => True
  | .cons q rest => Supported q a ∧ ArgumentsSupported rest a
end

end LogicLineages.OrdinalComparison.TerminationOrdering.ComparisonFreeVariables
