module
public import LogicLineages.OrdinalComparison.SourceTerms

@[expose] public section

/-! Independent structural obligations for the typed binding kernel used by
paper 06. These are prerequisites of its substitution-stability theorem, not
the stability theorem or the termination-ordering target itself. -/

namespace LogicLineages.OrdinalComparison.Source.Targets

def IdentityRenaming : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ : List Ty) (τ : Ty)
    (t : Term Symbol arity Γ τ), t.rename (fun v => v) = t

def ComposedRenaming : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ Δ Ξ : List Ty) (τ : Ty)
    (t : Term Symbol arity Γ τ) (ρ : Renaming Γ Δ) (π : Renaming Δ Ξ),
    (t.rename ρ).rename π = t.rename (fun v => π (ρ v))

def IdentitySubstitution : Prop :=
  ∀ (Symbol : Type) (arity : Symbol → Nat) (Γ : List Ty) (τ : Ty)
    (t : Term Symbol arity Γ τ), t.substitute (fun v => .var v) = t

end LogicLineages.OrdinalComparison.Source.Targets
