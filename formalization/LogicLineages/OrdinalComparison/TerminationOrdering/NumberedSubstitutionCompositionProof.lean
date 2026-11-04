module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSubstitutionCompositionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSubstitutionCompositionProof
open Source NumberedRewriteSyntax

theorem liftCompose {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta Theta : List Ty}
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (eta : NumberedRewriteSyntax.Substitution Symbol arity Delta Theta) (sigma : Ty) :
    (fun {tau} (v : Variable (sigma::Gamma) tau) => substitute (liftSubstitution theta v) (liftSubstitution eta)) =
    (fun {tau} (v : Variable (sigma::Gamma) tau) => liftSubstitution (fun v => substitute (theta v) eta) v) := by
  funext tau v
  cases v with
  | here => rfl
  | there v =>
    exact NumberedOpeningSubstitutionProof.actualTermWeakeningSubstitution Symbol arity Delta Theta eta sigma _ (theta v)

theorem substituteCompose {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau) : ∀ (Delta Theta : List Ty)
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (eta : NumberedRewriteSyntax.Substitution Symbol arity Delta Theta),
    substitute (substitute q theta) eta = substitute q (fun v => substitute (theta v) eta) := by
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => ∀ (Delta Theta : List Ty)
      (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
      (eta : NumberedRewriteSyntax.Substitution Symbol arity Delta Theta),
      substituteArguments (substituteArguments args theta) eta = substituteArguments args (fun v => substitute (theta v) eta))
  case var v => intros; rfl
  case lam body ih =>
    intro Delta Theta theta eta
    simp only [substitute]
    rw [ih _ _ (liftSubstitution theta) (liftSubstitution eta),liftCompose]
  case app f a ihf iha =>
    intro Delta Theta theta eta
    exact congrArg₂ AuxTerm.app (ihf Delta Theta theta eta) (iha Delta Theta theta eta)
  case bottom => intros; rfl
  case ordinary f base ih =>
    intro Delta Theta theta eta
    exact congrArg (AuxTerm.ordinary f) (ih Delta Theta theta eta)
  case numbered k f tau base types extras ihb ihe =>
    intro Delta Theta theta eta
    exact congrArg₂ (fun b e => AuxTerm.numbered k f tau b types e)
      (ihb Delta Theta theta eta) (ihe Delta Theta theta eta)
  case nil => intros; rfl
  case cons Gamma sigma types q rest ihq ihr Delta Theta theta eta =>
    exact congrArg₂ AuxArguments.cons (ihq Delta Theta theta eta) (ihr Delta Theta theta eta)

theorem actualTermSubstitutionComposition : NumberedSubstitutionCompositionTargets.ActualTermSubstitutionComposition := by
  intro Symbol arity Gamma Delta Theta theta eta tau q
  exact substituteCompose q Delta Theta theta eta

theorem actualArgumentSubstitutionComposition : NumberedSubstitutionCompositionTargets.ActualArgumentSubstitutionComposition := by
  intro Symbol arity Gamma Delta Theta theta eta types args
  induction types with
  | nil => cases args; rfl
  | cons tau types ih => cases args with
    | cons q rest => exact congrArg₂ AuxArguments.cons (substituteCompose q Delta Theta theta eta) (ih rest)

theorem actualBetaSubstitution : NumberedSubstitutionCompositionTargets.ActualBetaSubstitution := by
  intro Symbol arity Gamma Delta theta sigma tau body a
  rw [substituteCompose,substituteCompose]
  have he : (fun {upsilon} (v : Variable (sigma::Gamma) upsilon) => substitute (singleSubstitution a v) theta) =
      (fun {upsilon} (v : Variable (sigma::Gamma) upsilon) =>
        substitute (liftSubstitution theta v) (singleSubstitution (substitute a theta))) := by
    funext upsilon v
    cases v with
    | here => rfl
    | there v =>
      exact (NumberedRewriteApplicationBindingProof.weakeningCancellation Symbol arity Delta sigma upsilon
        (theta v) (substitute a theta)).symm
  rw [he]

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSubstitutionCompositionProof
