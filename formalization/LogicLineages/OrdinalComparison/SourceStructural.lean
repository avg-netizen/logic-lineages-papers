module
public import LogicLineages.OrdinalComparison.SourceStructuralTargets

@[expose] public section

namespace LogicLineages.OrdinalComparison.Source

theorem Renaming.lift_identity (Γ : List Ty) (τ : Ty) :
    @Renaming.lift Γ Γ τ (fun {σ : Ty} (v : Variable Γ σ) => v) =
      fun {σ : Ty} (v : Variable (τ :: Γ) σ) => v := by
  funext σ v
  cases v <;> rfl

theorem Renaming.lift_composition {Γ Δ Ξ : List Ty} (τ : Ty)
    (ρ : Renaming Γ Δ) (π : Renaming Δ Ξ) :
    @Renaming.lift Γ Ξ τ (fun v => π (ρ v)) =
      fun {σ : Ty} (v : Variable (τ :: Γ) σ) => π.lift (ρ.lift v) := by
  funext σ v
  cases v <;> rfl

theorem Term.rename_identity {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty}
    {τ : Ty} (t : Term Symbol arity Γ τ) : t.rename (fun v => v) = t := by
  induction t with
  | var v => rfl
  | app f a ihf iha => simp only [Term.rename, ihf, iha]
  | lam body ih => simp only [Term.rename, Renaming.lift_identity, ih]
  | zeroC => rfl
  | succC => rfl
  | caseC τ => rfl
  | recC τ => rfl
  | ranked s args ih =>
      change Term.ranked s (fun i => (args i).rename (fun v => v)) = .ranked s args
      congr 1
      funext i
      exact ih i

theorem identityRenaming : Targets.IdentityRenaming :=
  fun _ _ _ _ t => t.rename_identity

theorem Term.rename_composition {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty}
    {τ : Ty} (t : Term Symbol arity Γ τ) {Δ Ξ : List Ty}
    (ρ : Renaming Γ Δ) (π : Renaming Δ Ξ) :
    (t.rename ρ).rename π = t.rename (fun v => π (ρ v)) := by
  induction t generalizing Δ Ξ with
  | var v => rfl
  | app f a ihf iha => simp only [Term.rename, ihf, iha]
  | lam body ih =>
      simp only [Term.rename, ih, Renaming.lift_composition]
  | zeroC => rfl
  | succC => rfl
  | caseC τ => rfl
  | recC τ => rfl
  | ranked s args ih =>
      change Term.ranked s (fun i => ((args i).rename ρ).rename π) =
        .ranked s (fun i => (args i).rename (fun v => π (ρ v)))
      congr 1
      funext i
      exact ih i ρ π

theorem composedRenaming : Targets.ComposedRenaming :=
  fun _ _ _ _ _ _ t ρ π => t.rename_composition ρ π

theorem Substitution.lift_identity {Symbol : Type} (arity : Symbol → Nat)
    (Γ : List Ty) (τ : Ty) :
    @Substitution.lift Symbol arity Γ Γ τ (fun {σ : Ty} (v : Variable Γ σ) =>
      (Term.var v : Term Symbol arity Γ σ)) =
      fun {σ : Ty} (v : Variable (τ :: Γ) σ) =>
        (Term.var v : Term Symbol arity (τ :: Γ) σ) := by
  funext σ v
  cases v <;> rfl

theorem Term.substitute_identity {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty}
    {τ : Ty} (t : Term Symbol arity Γ τ) :
    t.substitute (fun v => .var v) = t := by
  induction t with
  | var v => rfl
  | app f a ihf iha => simp only [Term.substitute, ihf, iha]
  | lam body ih => simp only [Term.substitute, Substitution.lift_identity, ih]
  | zeroC => rfl
  | succC => rfl
  | caseC τ => rfl
  | recC τ => rfl
  | ranked s args ih =>
      change Term.ranked s (fun i => (args i).substitute (fun v => .var v)) =
        .ranked s args
      congr 1
      funext i
      exact ih i

theorem identitySubstitution : Targets.IdentitySubstitution :=
  fun _ _ _ _ t => t.substitute_identity

end LogicLineages.OrdinalComparison.Source
