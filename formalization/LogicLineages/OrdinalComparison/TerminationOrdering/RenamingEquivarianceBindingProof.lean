module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RenamingEquivarianceTargets
public import LogicLineages.OrdinalComparison.SourceMarkedBindingProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RenamingEquivarianceBindingProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding

theorem renameComposition {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) : ∀ (Δ Ξ : List Ty) (r : Renaming Γ Δ) (s : Renaming Δ Ξ),
    renameTerm (renameTerm q r) s=renameTerm q (fun v => s (r v)) := by
  induction q using MarkedTerm.rec
    (motive_2 := fun Γ types args => ∀ (Δ Ξ : List Ty) (r : Renaming Γ Δ) (s : Renaming Δ Ξ),
      renameArguments (renameArguments args r) s=renameArguments args (fun v => s (r v))) with
  | var v => intro Δ Ξ r s; rfl
  | lam body ih =>
      intro Δ Ξ r s
      apply congrArg MarkedTerm.lam
      rw [ih]
      apply congrArg (renameTerm body)
      funext σ v
      cases v <;> rfl
  | ordinary hd args ih =>
      intro Δ Ξ r s
      exact congrArg (MarkedTerm.ordinary hd) (ih Δ Ξ r s)
  | marked hd out args types extras iha ihe =>
      intro Δ Ξ r s
      exact congrArg₂ (fun a e => MarkedTerm.marked hd out a types e) (iha Δ Ξ r s) (ihe Δ Ξ r s)
  | nil => rfl
  | cons q rest ihq ihr =>
      rename_i Δ Ξ r s
      exact congrArg₂ Arguments.cons (ihq Δ Ξ r s) (ihr Δ Ξ r s)

theorem renameArgumentsComposition {Symbol : Type} {arity : Symbol → Nat} {Γ Δ Ξ types : List Ty}
    (args : Arguments Symbol arity Γ types) (r : Renaming Γ Δ) (s : Renaming Δ Ξ) :
    renameArguments (renameArguments args r) s=renameArguments args (fun v => s (r v)) := by
  induction types with
  | nil => cases args; rfl
  | cons σ types ih =>
      cases args with
      | cons q rest => exact congrArg₂ Arguments.cons (renameComposition q Δ Ξ r s) (ih rest)

theorem substitutionCovariance : RenamingEquivarianceTargets.SubstitutionCovariance := by
  intro Symbol arity Γ Γ' Δ Δ' τ q
  induction q using MarkedTerm.rec
    (motive_2 := fun Γ types args => ∀ (Γ' Δ Δ' : List Ty)
      (r : Renaming Γ Γ') (s : Renaming Δ Δ')
      (env : MarkedSubstitution Symbol arity Γ Δ) (env' : MarkedSubstitution Symbol arity Γ' Δ'),
      (∀ {σ} (v : Variable Γ σ),env' (r v)=renameTerm (env v) s) →
      substituteArguments (renameArguments args r) env'=renameArguments (substituteArguments args env) s)
    generalizing Γ' Δ Δ' with
  | var v => intro r s env env' h; exact h v
  | lam body ih =>
      intro r s env env' h
      apply congrArg MarkedTerm.lam
      apply ih _ _ _ r.lift s.lift (liftSubstitution env) (liftSubstitution env')
      intro σ v
      cases v with
      | here => rfl
      | there v =>
          simp only [Renaming.lift,liftSubstitution,h]
          rw [renameComposition,renameComposition]
          rfl
  | ordinary hd args ih =>
      intro r s env env' h
      exact congrArg (MarkedTerm.ordinary hd) (ih Γ' Δ Δ' r s env env' h)
  | marked hd out args types extras iha ihe =>
      intro r s env env' h
      exact congrArg₂ (fun a e => MarkedTerm.marked hd out a types e)
        (iha Γ' Δ Δ' r s env env' h) (ihe Γ' Δ Δ' r s env env' h)
  | nil => rfl
  | cons q rest ihq ihr =>
      rename_i Γ' Δ Δ' r s env env' h
      exact congrArg₂ Arguments.cons (ihq Γ' Δ Δ' r s env env' h) (ihr Γ' Δ Δ' r s env env' h)

theorem argumentsCovariance {Symbol : Type} {arity : Symbol → Nat} {Γ Γ' Δ Δ' types : List Ty}
    (args : Arguments Symbol arity Γ types) (r : Renaming Γ Γ') (s : Renaming Δ Δ')
    (env : MarkedSubstitution Symbol arity Γ Δ) (env' : MarkedSubstitution Symbol arity Γ' Δ')
    (h : ∀ {σ} (v : Variable Γ σ),env' (r v)=renameTerm (env v) s) :
    substituteArguments (renameArguments args r) env'=renameArguments (substituteArguments args env) s := by
  induction types with
  | nil => cases args; rfl
  | cons σ types ih =>
      cases args with
      | cons q rest => exact congrArg₂ Arguments.cons (substitutionCovariance Symbol arity Γ Γ' Δ Δ' _ q r s env env' h) (ih rest)

theorem renameAppend {Symbol : Type} {arity : Symbol → Nat} {Γ Δ xs ys : List Ty}
    (a : Arguments Symbol arity Γ xs) (b : Arguments Symbol arity Γ ys) (r : Renaming Γ Δ) :
    renameArguments (appendArguments a b) r=appendArguments (renameArguments a r) (renameArguments b r) := by
  induction xs with
  | nil => cases a; rfl
  | cons σ xs ih =>
      cases a with
      | cons q rest => exact congrArg (Arguments.cons (renameTerm q r)) (ih rest)

end LogicLineages.OrdinalComparison.TerminationOrdering.RenamingEquivarianceBindingProof
