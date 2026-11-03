module
public import LogicLineages.OrdinalComparison.TerminationOrdering.HeadClosureDefinitions
public import LogicLineages.OrdinalComparison.SourceTypeSupportDefinitions

@[expose] public section
/-! Literal marked-syntax type confinement. Only actual node result/binder and
argument types are inspected: unused ambient variables and a marked head's
former output type are not added. This is not a comparison relation. -/
namespace LogicLineages.OrdinalComparison.TerminationOrdering
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding

def SubtypeClosed (K : Ty → Prop) : Prop :=
  ∀ σ, K σ → ∀ τ ∈ σ.subtypes, K τ

mutual
def typesAllowed {Symbol : Type} {arity : Symbol → Nat}
    (K : Ty → Prop) {Γ : List Ty} {τ : Ty} : MarkedTerm Symbol arity Γ τ → Prop
  | .var _ => K τ
  | .lam (σ := σ) body => K τ ∧ K σ ∧ typesAllowed K body
  | .ordinary _ base => K τ ∧ argumentTypesAllowed K base
  | .marked _ _ base _ extras =>
      K τ ∧ argumentTypesAllowed K base ∧ argumentTypesAllowed K extras
def argumentTypesAllowed {Symbol : Type} {arity : Symbol → Nat}
    (K : Ty → Prop) {Γ types : List Ty} : Arguments Symbol arity Γ types → Prop
  | .nil => True
  | .cons q rest => typesAllowed K q ∧ argumentTypesAllowed K rest
end

def substitutionTypesAllowed {Symbol : Type} {arity : Symbol → Nat}
    (K : Ty → Prop) {Γ Δ : List Ty}
    (env : MarkedSubstitution Symbol arity Γ Δ) : Prop :=
  ∀ {σ : Ty} (v : Variable Γ σ), K σ → typesAllowed K (env v)

end LogicLineages.OrdinalComparison.TerminationOrdering
