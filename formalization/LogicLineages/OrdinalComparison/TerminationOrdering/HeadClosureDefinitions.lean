module
public import LogicLineages.OrdinalComparison.SourceSpecialApplicationDefinitions

@[expose] public section

/-! Literal head-occurrence invariants for paper06's existing marked syntax.
The predicate inspects every real base/extra argument; arbitrary retyping does
not add a new head. This is a supplier to finite closure, not a definition of
the comparison relation or a substitute for its full closure theorem. -/
namespace LogicLineages.OrdinalComparison.TerminationOrdering
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding

mutual
def headsAllowed {Symbol : Type} {arity : Symbol → Nat}
    (P : Head Symbol → Prop) {Γ : List Ty} {τ : Ty} :
    MarkedTerm Symbol arity Γ τ → Prop
  | .var _ => True
  | .lam body => headsAllowed P body
  | .ordinary h base => P h ∧ argumentsAllowed P base
  | .marked h _ base _ extras => P h ∧ argumentsAllowed P base ∧ argumentsAllowed P extras
def argumentsAllowed {Symbol : Type} {arity : Symbol → Nat}
    (P : Head Symbol → Prop) {Γ types : List Ty} :
    Arguments Symbol arity Γ types → Prop
  | .nil => True
  | .cons q rest => headsAllowed P q ∧ argumentsAllowed P rest
end

def substitutionAllowed {Symbol : Type} {arity : Symbol → Nat}
    (P : Head Symbol → Prop) {Γ Δ : List Ty}
    (env : MarkedSubstitution Symbol arity Γ Δ) : Prop :=
  ∀ {σ : Ty} (v : Variable Γ σ), headsAllowed P (env v)

end LogicLineages.OrdinalComparison.TerminationOrdering
