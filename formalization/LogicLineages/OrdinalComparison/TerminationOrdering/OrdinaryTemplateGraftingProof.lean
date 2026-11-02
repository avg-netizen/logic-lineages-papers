module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryTemplateGraftingTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.RenamingEquivarianceProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryTemplateGraftingProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open RecursiveComparison OrdinaryTemplateGrafting

private theorem groundGrafting {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : List Ty}
    (above : Symbol → Symbol → Prop) (n : Nat) (f : Fin n → MarkedTerm Symbol arity Γ .ground)
    (env env' : MarkedSubstitution Symbol arity Γ Δ)
    (h : ∀ i, Weak Symbol arity above Δ ⟨.ground,substituteTerm (f i) env⟩ ⟨.ground,substituteTerm (f i) env'⟩) :
    WeakMatch Symbol arity above Δ
      (argumentList (substituteArguments (groundArguments n f) env))
      (argumentList (substituteArguments (groundArguments n f) env')) := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .cons _ _ _ _ (h 0) (ih (fun i => f i.succ) (fun i => h i.succ))

theorem environmentGrafting : OrdinaryTemplateGraftingTargets.EnvironmentGrafting := by
  intro Symbol arity above Γ Δ τ A
  induction A generalizing Δ with
  | var v => intro env env' h; exact h v
  | app f a ihf iha =>
      intro env env' h
      apply Weak.fun_ (.application _ _) (.application _ _)
        (.cons (substituteTerm (embed f) env) (.cons (substituteTerm (embed a) env) .nil))
        (.cons (substituteTerm (embed f) env') (.cons (substituteTerm (embed a) env') .nil)) _ rfl rfl (.refl _)
      exact .cons _ _ _ _ (ihf Δ env env' h) (.cons _ _ _ _ (iha Δ env env' h) .nil)
  | lam body ih =>
      intro env env' h
      apply Weak.abs
      apply ih _ (liftSubstitution env) (liftSubstitution env')
      intro σ v
      cases v with
      | here => exact .var .here
      | there v => exact RenamingEquivarianceProof.weakCovariance Symbol arity above Δ _ (Renaming.weaken Δ _) _ _ (h v)
  | zeroC => intro env env' h; exact .fun_ .zero .zero .nil .nil [] rfl rfl (.refl _) .nil
  | succC => intro env env' h; exact .fun_ .succ .succ .nil .nil [] rfl rfl (.refl _) .nil
  | caseC τ => intro env env' h; exact .fun_ (.cases τ) (.cases τ) .nil .nil [] rfl rfl (.refl _) .nil
  | recC τ => intro env env' h; exact .fun_ (.recursor τ) (.recursor τ) .nil .nil [] rfl rfl (.refl _) .nil
  | ranked f args ih =>
      intro env env' h
      apply Weak.fun_ (.ranked f) (.ranked f)
        (substituteArguments (groundArguments (arity f) (fun i => embed (args i))) env)
        (substituteArguments (groundArguments (arity f) (fun i => embed (args i))) env') _ rfl rfl (.refl _)
      exact groundGrafting above (arity f) (fun i => embed (args i)) env env' (fun i => ih i Δ env env' h)

theorem distinguishedVariableGrafting : OrdinaryTemplateGraftingTargets.DistinguishedVariableGrafting := by
  intro Symbol arity above Γ σ τ A p q h
  apply environmentGrafting Symbol arity above (σ::Γ) Γ τ A
  intro υ v
  cases v with
  | here => exact h
  | there v => exact .var v

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryTemplateGraftingProof
