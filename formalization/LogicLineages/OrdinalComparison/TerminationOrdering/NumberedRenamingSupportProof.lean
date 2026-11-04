module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRenamingSupportSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRenamingSupportProof
open Source NumberedRewriteSyntax NumberedRenamingSupport NumberedRenamingSupportSupportProof

theorem supportedPreimage {Symbol : Type} {arity : Symbol → Nat} {Delta : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Delta tau) : ∀ (Gamma : List Ty) (rho : Renaming Gamma Delta),
    supports (rangePredicate rho) q → ∃ source : AuxTerm Symbol arity Gamma tau, NumberedRewriteSyntax.rename source rho = q := by
  induction q using AuxTerm.rec
    (motive_2 := fun Delta types args => ∀ (Gamma : List Ty) (rho : Renaming Gamma Delta),
      supportsArguments (rangePredicate rho) args → ∃ source : AuxArguments Symbol arity Gamma types, renameArguments source rho = args)
  case var v =>
    intro Gamma rho h
    obtain ⟨w,hw⟩ := h
    exact ⟨.var w,congrArg AuxTerm.var hw⟩
  case lam body ih =>
    intro Gamma rho h
    have hr : supports (rangePredicate rho.lift) body := by
      rw [← liftRangePredicate]
      exact h
    obtain ⟨source,he⟩ := ih _ rho.lift hr
    exact ⟨.lam source,congrArg AuxTerm.lam he⟩
  case app f a ihf iha =>
    intro Gamma rho h
    obtain ⟨f0,hf⟩ := ihf Gamma rho h.1
    obtain ⟨a0,ha⟩ := iha Gamma rho h.2
    exact ⟨.app f0 a0,congrArg₂ AuxTerm.app hf ha⟩
  case bottom tau => intro Gamma rho h; exact ⟨.bottom tau,rfl⟩
  case ordinary f base ih =>
    intro Gamma rho h
    obtain ⟨base0,hb⟩ := ih Gamma rho h
    exact ⟨.ordinary f base0,congrArg (AuxTerm.ordinary f) hb⟩
  case numbered k f tau base types extras ihb ihe =>
    intro Gamma rho h
    obtain ⟨base0,hb⟩ := ihb Gamma rho h.1
    obtain ⟨extras0,he⟩ := ihe Gamma rho h.2
    exact ⟨.numbered k f tau base0 types extras0,congrArg₂ (fun b e => AuxTerm.numbered k f tau b types e) hb he⟩
  case nil => intros; exact ⟨.nil,rfl⟩
  case cons Delta sigma types q rest ihq ihr Gamma rho h =>
    obtain ⟨q0,hq⟩ := ihq Gamma rho h.1
    obtain ⟨rest0,hr⟩ := ihr Gamma rho h.2
    exact ⟨.cons q0 rest0,congrArg₂ AuxArguments.cons hq hr⟩

theorem actualLiftRange : NumberedRenamingSupportTargets.ActualLiftRange := liftRange

theorem actualTermSupportImage : NumberedRenamingSupportTargets.ActualTermSupportImage := by
  intro Symbol arity Gamma Delta rho tau q
  constructor
  · exact supportedPreimage q Gamma rho
  · rintro ⟨source,rfl⟩
    exact renamedSupported source Delta rho

theorem actualArgumentSupportImage : NumberedRenamingSupportTargets.ActualArgumentSupportImage := by
  intro Symbol arity Gamma Delta rho types args
  constructor
  · intro h
    induction types with
    | nil => cases args; exact ⟨.nil,rfl⟩
    | cons tau types ih => cases args with
      | cons q rest =>
        obtain ⟨q0,hq⟩ := supportedPreimage q Gamma rho h.1
        obtain ⟨rest0,hr⟩ := ih rest h.2
        exact ⟨.cons q0 rest0,congrArg₂ AuxArguments.cons hq hr⟩
  · rintro ⟨source,rfl⟩
    exact renamedArgumentsSupported source Delta rho

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRenamingSupportProof
