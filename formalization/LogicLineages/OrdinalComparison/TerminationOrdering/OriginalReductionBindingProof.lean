module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalReductionTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OriginalReductionBindingProof
open Source

theorem renameComposition {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (q : Term Symbol arity Γ τ) : ∀ (Δ Ξ : List Ty) (r : Renaming Γ Δ) (s : Renaming Δ Ξ),
    (q.rename r).rename s=q.rename (fun v => s (r v)) := by
  induction q with
  | var v => intro Δ Ξ r s; rfl
  | app f a ihf iha => intro Δ Ξ r s; exact congrArg₂ Term.app (ihf Δ Ξ r s) (iha Δ Ξ r s)
  | lam body ih =>
      intro Δ Ξ r s
      apply congrArg Term.lam
      rw [ih]
      apply congrArg (Term.rename body)
      funext σ v
      cases v <;> rfl
  | zeroC => intros; rfl
  | succC => intros; rfl
  | caseC => intros; rfl
  | recC => intros; rfl
  | ranked f args ih =>
      intro Δ Ξ r s
      apply congrArg (Term.ranked f)
      funext i
      exact ih i Δ Ξ r s

theorem substitutionCovariance {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (q : Term Symbol arity Γ τ) : ∀ (Γ' Δ Δ' : List Ty) (r : Renaming Γ Γ') (s : Renaming Δ Δ')
    (env : Substitution Symbol arity Γ Δ) (env' : Substitution Symbol arity Γ' Δ'),
    (∀ {σ} (v : Variable Γ σ),env' (r v)=(env v).rename s) →
    (q.rename r).substitute env'=(q.substitute env).rename s := by
  induction q with
  | var v => intro Γ' Δ Δ' r s env env' h; exact h v
  | app f a ihf iha =>
      intro Γ' Δ Δ' r s env env' h
      exact congrArg₂ Term.app (ihf Γ' Δ Δ' r s env env' h) (iha Γ' Δ Δ' r s env env' h)
  | lam body ih =>
      intro Γ' Δ Δ' r s env env' h
      apply congrArg Term.lam
      apply ih _ _ _ r.lift s.lift env.lift env'.lift
      intro σ v
      cases v with
      | here => rfl
      | there v =>
          simp only [Renaming.lift,Substitution.lift,h]
          rw [renameComposition,renameComposition]
          rfl
  | zeroC => intros; rfl
  | succC => intros; rfl
  | caseC => intros; rfl
  | recC => intros; rfl
  | ranked f args ih =>
      intro Γ' Δ Δ' r s env env' h
      apply congrArg (Term.ranked f)
      funext i
      exact ih i Γ' Δ Δ' r s env env' h

theorem substitutionComposition {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (q : Term Symbol arity Γ τ) : ∀ (Δ Ξ : List Ty)
    (env : Substitution Symbol arity Γ Δ) (env' : Substitution Symbol arity Δ Ξ),
    (q.substitute env).substitute env'=q.substitute (fun v => (env v).substitute env') := by
  induction q with
  | var v => intros; rfl
  | app f a ihf iha => intro Δ Ξ env env'; exact congrArg₂ Term.app (ihf Δ Ξ env env') (iha Δ Ξ env env')
  | lam body ih =>
      intro Δ Ξ env env'
      apply congrArg Term.lam
      rw [ih]
      apply congrArg (Term.substitute body)
      funext σ v
      cases v with
      | here => rfl
      | there v =>
          exact substitutionCovariance (env v) _ _ _ (Renaming.weaken Δ _) (Renaming.weaken Ξ _)
            env' env'.lift (by intros; rfl)
  | zeroC => intros; rfl
  | succC => intros; rfl
  | caseC => intros; rfl
  | recC => intros; rfl
  | ranked f args ih =>
      intro Δ Ξ env env'
      apply congrArg (Term.ranked f)
      funext i
      exact ih i Δ Ξ env env'

theorem restoreRenaming {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (q : Term Symbol arity Γ τ) : ∀ (Δ : List Ty) (r : Renaming Γ Δ) (env : Substitution Symbol arity Δ Γ),
    (∀ {σ} (v : Variable Γ σ),env (r v)=.var v) → (q.rename r).substitute env=q := by
  induction q with
  | var v => intro Δ r env h; exact h v
  | app f a ihf iha => intro Δ r env h; exact congrArg₂ Term.app (ihf Δ r env h) (iha Δ r env h)
  | lam body ih =>
      intro Δ r env h
      apply congrArg Term.lam
      apply ih _ r.lift env.lift
      intro σ v
      cases v with
      | here => rfl
      | there v => simp only [Renaming.lift,Substitution.lift,h,Term.rename,Renaming.weaken]
  | zeroC => intros; rfl
  | succC => intros; rfl
  | caseC => intros; rfl
  | recC => intros; rfl
  | ranked f args ih =>
      intro Δ r env h
      apply congrArg (Term.ranked f)
      funext i
      exact ih i Δ r env h

theorem betaSubstitutionFusion {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : List Ty} {σ τ : Ty}
    (body : Term Symbol arity (σ::Γ) τ) (arg : Term Symbol arity Γ σ) (θ : Substitution Symbol arity Γ Δ) :
    (body.substitute θ.lift).substitute (Substitution.single (arg.substitute θ))=
      (body.substitute (Substitution.single arg)).substitute θ := by
  rw [substitutionComposition,substitutionComposition]
  apply congrArg (Term.substitute body)
  funext υ v
  cases v with
  | here => rfl
  | there v => exact restoreRenaming (θ v) _ (Renaming.weaken Δ σ) (Substitution.single (arg.substitute θ)) (by intros; rfl)

end LogicLineages.OrdinalComparison.TerminationOrdering.OriginalReductionBindingProof
