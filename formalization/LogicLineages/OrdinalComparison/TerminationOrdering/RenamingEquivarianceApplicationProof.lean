module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RenamingEquivarianceBindingProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RenamingEquivarianceApplicationProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open RenamingEquivarianceBindingProof

private theorem emptyWith {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) (env : MarkedSubstitution Symbol arity Γ Δ) :
    applyOriginalWith q env .nil rfl=some (substituteTerm q env) := by
  cases q <;> rfl

private theorem emptyCovariance {Symbol : Type} {arity : Symbol → Nat} {Γ Γ' Δ Δ' : List Ty} {σ τ : Ty}
    (q : MarkedTerm Symbol arity Γ σ) (r : Renaming Γ Γ') (s : Renaming Δ Δ')
    (env : MarkedSubstitution Symbol arity Γ Δ) (env' : MarkedSubstitution Symbol arity Γ' Δ')
    (suffix : σ=arrows [] τ) (h : ∀ {υ} (v : Variable Γ υ),env' (r v)=renameTerm (env v) s) :
    applyOriginalWith (renameTerm q r) env' .nil suffix=
      (applyOriginalWith q env .nil suffix).map (fun out => renameTerm out s) := by
  cases suffix
  exact (emptyWith (renameTerm q r) env').trans
    ((congrArg some (substitutionCovariance Symbol arity Γ Γ' Δ Δ' _ q r s env env' h)).trans
      (congrArg (Option.map (fun out => renameTerm out s)) (emptyWith q env)).symm)

theorem originalApplyCovariance : RenamingEquivarianceTargets.OriginalApplyCovariance := by
  intro Symbol arity Γ Γ' Δ Δ' σ τ types q
  induction q using MarkedTerm.rec (motive_2 := fun _ _ _ => True) generalizing Γ' Δ Δ' τ types with
  | var v =>
      intro args r s env env' suffix h
      cases args with
      | nil => exact emptyCovariance (.var v) r s env env' suffix h
      | cons a rest => rfl
  | lam body ih =>
      intro args r s env env' suffix h
      cases args with
      | nil => exact emptyCovariance (.lam body) r s env env' suffix h
      | cons a rest =>
          obtain ⟨h1,h2⟩ := Ty.arrow.inj suffix
          cases h1
          cases h2
          apply ih _ _ _ _ _ rest r.lift s
            (extendEnvironment env a) (extendEnvironment env' (renameTerm a s)) rfl
          intro υ v
          cases v with
          | here => rfl
          | there v => exact h v
  | ordinary hd base ih =>
      intro args r s env env' suffix h
      cases args with
      | nil => exact emptyCovariance (.ordinary hd base) r s env env' suffix h
      | cons a rest =>
          simp only [renameTerm,renameArguments,applyOriginalWith,Option.map_some]
          rw [argumentsCovariance base r s env env' h]
  | marked hd out base extraTypes extras ihb ihe =>
      intro args r s env env' suffix h
      cases args with
      | nil => exact emptyCovariance (.marked hd out base extraTypes extras) r s env env' suffix h
      | cons a rest =>
          simp only [renameTerm,renameArguments,applyOriginalWith,Option.map_some]
          rw [argumentsCovariance base r s env env' h,argumentsCovariance extras r s env env' h,
            renameAppend]
          rfl
  | nil => trivial
  | cons q rest ihq ihr => trivial

end LogicLineages.OrdinalComparison.TerminationOrdering.RenamingEquivarianceApplicationProof
