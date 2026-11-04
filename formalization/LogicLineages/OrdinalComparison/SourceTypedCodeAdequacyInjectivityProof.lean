module
public import LogicLineages.OrdinalComparison.SourceTypedCodeAdequacyTypesProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceTypedCodeAdequacy.Proof
open SyntaxCode

theorem erase_injective {Γ τ} (t : OriginalTerm Γ τ) : ∀ u : OriginalTerm Γ τ,erase t=erase u → t=u := by
  induction t with
  | var x =>
    intro u h
    cases u with
    | var y => exact congrArg Term.var (variable_index_injective x y (Raw.var.inj h))
    | app f a => cases h
    | lam b => cases h
    | zeroC => cases h
    | succC => cases h
    | caseC σ => cases h
    | recC σ => cases h
    | ranked tag args => cases tag
  | @app Γ σ τ f a ihf iha =>
    intro u h
    cases u with
    | @app _ υ _ g b =>
      have hp := Raw.app.inj h
      have hs : σ=υ := (Ty.arrow.inj (fixedContextTypeUniqueness Γ (.arrow σ τ) (.arrow υ τ) f g hp.1)).1
      cases hs
      exact congrArg₂ Term.app (ihf g hp.1) (iha b hp.2)
    | var y => cases h
    | lam b => cases h
    | zeroC => cases h
    | succC => cases h
    | caseC υ => cases h
    | recC υ => cases h
    | ranked tag args => cases tag
  | lam t ih =>
    intro u h
    cases u with
    | lam v => exact congrArg Term.lam (ih v (Raw.lam.inj h).2)
    | var y => cases h
    | app f a => cases h
    | succC => cases h
    | caseC υ => cases h
    | recC υ => cases h
  | zeroC =>
    intro u h
    cases u with
    | zeroC => rfl
    | var y => cases h
    | app f a => cases h
    | ranked tag args => cases tag
  | succC =>
    intro u h
    cases u with
    | succC => rfl
    | var y => cases h
    | app f a => cases h
    | lam b => cases h
  | caseC σ =>
    intro u h
    cases u with
    | caseC υ =>
      have ht := type_code_injective (Raw.caseC.inj h)
      cases ht
      rfl
    | var y => cases h
    | app f a => cases h
    | lam b => cases h
  | recC σ =>
    intro u h
    cases u with
    | recC υ =>
      have ht := type_code_injective (Raw.recC.inj h)
      cases ht
      rfl
    | var y => cases h
    | app f a => cases h
    | lam b => cases h
  | ranked tag args ih => cases tag

theorem typedCodeInjective : Targets.TypedCodeInjective := by
  intro Γ τ t u h
  exact erase_injective t u (SyntaxCode.Proof.codeInjective h)
end LogicLineages.OrdinalComparison.Source.SourceTypedCodeAdequacy.Proof
