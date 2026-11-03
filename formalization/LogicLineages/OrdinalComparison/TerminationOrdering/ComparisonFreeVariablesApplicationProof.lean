module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ComparisonFreeVariablesSyntaxProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ComparisonFreeVariablesApplicationProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open ComparisonFreeVariables ComparisonFreeVariablesSyntaxProof

private theorem emptyWith {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) (env : MarkedSubstitution Symbol arity Γ Δ) :
    applyOriginalWith q env .nil rfl=some (substituteTerm q env) := by cases q <;> rfl

private theorem emptyProvenance {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : List Ty} {σ τ : Ty}
    (q : MarkedTerm Symbol arity Γ σ) (env : MarkedSubstitution Symbol arity Γ Δ)
    (suffix : σ=arrows [] τ) (r : MarkedTerm Symbol arity Δ τ) (a : Allowed Γ) (b : Allowed Δ)
    (hq : Supported q a) (henv : ∀ {υ} (v : Variable Γ υ),a v → Supported (env v) b)
    (he : applyOriginalWith q env .nil suffix=some r) : Supported r b := by
  cases suffix
  have hr : substituteTerm q env=r := Option.some.inj ((emptyWith q env).symm.trans he)
  subst r
  exact substituteSupported q a hq Δ env b henv

theorem originalApplyProvenance : ComparisonFreeVariablesTargets.OriginalApplyProvenance := by
  intro Symbol arity Γ Δ σ τ types q
  induction q using MarkedTerm.rec (motive_2 := fun _ _ _ => True) generalizing Δ τ types with
  | var v =>
      intro env args suffix r a b hq henv hargs he
      cases args with
      | nil => exact emptyProvenance (.var v) env suffix r a b hq henv he
      | cons p rest => cases he
  | lam body ih =>
      intro env args suffix r a b hq henv hargs he
      cases args with
      | nil => exact emptyProvenance (.lam body) env suffix r a b hq henv he
      | cons p rest =>
          obtain ⟨h1,h2⟩ := Ty.arrow.inj suffix
          cases h1
          cases h2
          apply ih _ _ _ (extendEnvironment env p) rest rfl r (liftAllowed a) b hq
          · intro υ v hv
            cases v with
            | here => exact hargs.1
            | there v => exact henv v hv
          · exact hargs.2
          · exact he
  | ordinary hd base ih =>
      intro env args suffix r a b hq henv hargs he
      cases args with
      | nil => exact emptyProvenance (.ordinary hd base) env suffix r a b hq henv he
      | cons p rest =>
          have hr : MarkedTerm.marked hd _ (substituteArguments base env) _ (.cons p rest)=r := Option.some.inj he
          subst r
          exact ⟨substituteArgumentsSupported base a b env hq henv,hargs⟩
  | marked hd out base extraTypes extras ihb ihe =>
      intro env args suffix r a b hq henv hargs he
      cases args with
      | nil => exact emptyProvenance (.marked hd out base extraTypes extras) env suffix r a b hq henv he
      | cons p rest =>
          have hr : MarkedTerm.marked hd _ (substituteArguments base env) _
            (appendArguments (substituteArguments extras env) (.cons p rest))=r := Option.some.inj he
          subst r
          exact ⟨substituteArgumentsSupported base a b env hq.1 henv,
            (appendSupported _ _ b).mpr ⟨substituteArgumentsSupported extras a b env hq.2 henv,hargs⟩⟩
  | nil => trivial
  | cons q rest ihq ihr => trivial

end LogicLineages.OrdinalComparison.TerminationOrdering.ComparisonFreeVariablesApplicationProof
