module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimarySubstitutionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimarySubstitutionProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowEquivalence NumberedPrimarySubstitution

theorem argumentListSubstitute {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta types : List Ty}
    (args : AuxArguments Symbol arity Gamma types) (rho : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta) :
    argumentList (substituteArguments args rho) = (argumentList args).map (substitutePacked rho) := by
  induction types with
  | nil => cases args; rfl
  | cons tau types ih => cases args with
    | cons q rest => simp only [substituteArguments,argumentList,List.map_cons,substitutePacked,ih rest]

theorem substitutePrimary {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S Gamma : List Ty}
    {q r : Packed Symbol arity Gamma} (h : WindowPrimary Symbol arity symbols S Gamma q r) :
    ∀ (Delta : List Ty) (rho : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
      WindowPrimary Symbol arity symbols S Delta (substitutePacked rho q) (substitutePacked rho r) := by
  induction h using WindowPrimary.rec
    (motive_2 := fun Gamma types base target _ => ∀ (Delta : List Ty)
      (rho : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
      WindowArgumentPrimary Symbol arity symbols S Delta types (substituteArguments base rho) (substituteArguments target rho))
  case refl q => intro Delta rho; exact .refl _
  case symm h ih => intro Delta rho; exact .symm (ih Delta rho)
  case trans h1 h2 ih1 ih2 => intro Delta rho; exact .trans (ih1 Delta rho) (ih2 Delta rho)
  case ordinary f g base target hf hg he ht hp =>
    intro Delta rho
    apply WindowPrimary.ordinary f g _ _ hf hg he ht
    rw [argumentListSubstitute,argumentListSubstitute]
    exact hp.map (substitutePacked rho)
  case numbered k f g tau base target types extras hf hg he hp =>
    intro Delta rho
    apply WindowPrimary.numbered k f g tau _ _ types _ hf hg he
    rw [argumentListSubstitute,argumentListSubstitute]
    exact hp.map (substitutePacked rho)
  case lam q r h ih => intro Delta rho; exact .lam _ _ (ih _ (liftSubstitution rho))
  case appFunction q r a h ih => intro Delta rho; exact .appFunction _ _ _ (ih Delta rho)
  case appArgument q a b h ih => intro Delta rho; exact .appArgument _ _ _ (ih Delta rho)
  case ordinaryArguments f base target h ih => intro Delta rho; exact .ordinaryArguments f _ _ (ih Delta rho)
  case numberedBase k f tau base target types extras h ih => intro Delta rho; exact .numberedBase k f tau _ _ types _ (ih Delta rho)
  case numberedExtras k f tau base types extras target h ih => intro Delta rho; exact .numberedExtras k f tau _ types _ _ (ih Delta rho)
  case nil => exact .nil
  case cons Gamma sigma types q r rest target hq ht ihq iht Delta rho =>
    exact .cons _ _ _ _ (ihq Delta rho) (iht Delta rho)

theorem actualPrimarySubstitution : NumberedPrimarySubstitutionTargets.ActualPrimarySubstitution := by
  intro Symbol arity symbols S Gamma Delta rho q r h
  exact substitutePrimary h Delta rho

theorem actualArgumentPrimarySubstitution : NumberedPrimarySubstitutionTargets.ActualArgumentPrimarySubstitution := by
  intro Symbol arity symbols S Gamma Delta types rho base target h
  induction types with
  | nil => cases h; exact .nil
  | cons tau types ih => cases h with
    | cons q r rest target hq ht =>
      exact .cons _ _ _ _ (substitutePrimary hq Delta rho) (ih rest target ht)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimarySubstitutionProof
