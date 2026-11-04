module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMixedBindingTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMixedBindingProof
open Source NumberedRewriteSyntax

theorem liftSubRename {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta Theta : List Ty}
    (rho : Renaming Gamma Delta) (theta : NumberedRewriteSyntax.Substitution Symbol arity Delta Theta) (sigma : Ty) :
    (fun {tau} (v : Variable (sigma::Gamma) tau) => liftSubstitution theta (rho.lift v)) =
    (fun {tau} (v : Variable (sigma::Gamma) tau) => liftSubstitution (fun v => theta (rho v)) v) := by
  funext tau v
  cases v <;> rfl

theorem liftRenameSub {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta Theta : List Ty}
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta) (rho : Renaming Delta Theta) (sigma : Ty) :
    (fun {tau} (v : Variable (sigma::Gamma) tau) => NumberedRewriteSyntax.rename (liftSubstitution theta v) rho.lift) =
    (fun {tau} (v : Variable (sigma::Gamma) tau) => liftSubstitution (fun v => NumberedRewriteSyntax.rename (theta v) rho) v) := by
  funext tau v
  cases v with
  | here => rfl
  | there v =>
    change NumberedRewriteSyntax.rename (NumberedRewriteSyntax.rename (theta v) (Renaming.weaken Delta sigma)) rho.lift =
      NumberedRewriteSyntax.rename (NumberedRewriteSyntax.rename (theta v) rho) (Renaming.weaken Theta sigma)
    rw [NumberedRenamingCompositionProof.renameCompose,NumberedRenamingCompositionProof.renameCompose]
    rfl

theorem substituteRename {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau) : ∀ (Delta Theta : List Ty) (rho : Renaming Gamma Delta)
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Delta Theta),
    substitute (NumberedRewriteSyntax.rename q rho) theta = substitute q (fun v => theta (rho v)) := by
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => ∀ (Delta Theta : List Ty) (rho : Renaming Gamma Delta)
      (theta : NumberedRewriteSyntax.Substitution Symbol arity Delta Theta),
      substituteArguments (renameArguments args rho) theta = substituteArguments args (fun v => theta (rho v)))
  case var v => intros; rfl
  case lam body ih =>
    intro Delta Theta rho theta
    simp only [NumberedRewriteSyntax.rename,substitute]
    rw [ih _ _ rho.lift (liftSubstitution theta),liftSubRename]
  case app f a ihf iha =>
    intro Delta Theta rho theta
    exact congrArg₂ AuxTerm.app (ihf Delta Theta rho theta) (iha Delta Theta rho theta)
  case bottom => intros; rfl
  case ordinary f base ih =>
    intro Delta Theta rho theta
    exact congrArg (AuxTerm.ordinary f) (ih Delta Theta rho theta)
  case numbered k f tau base types extras ihb ihe =>
    intro Delta Theta rho theta
    exact congrArg₂ (fun b e => AuxTerm.numbered k f tau b types e)
      (ihb Delta Theta rho theta) (ihe Delta Theta rho theta)
  case nil => intros; rfl
  case cons Gamma sigma types q rest ihq ihr Delta Theta rho theta =>
    exact congrArg₂ AuxArguments.cons (ihq Delta Theta rho theta) (ihr Delta Theta rho theta)

theorem renameSubstitute {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau) : ∀ (Delta Theta : List Ty)
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta) (rho : Renaming Delta Theta),
    NumberedRewriteSyntax.rename (substitute q theta) rho = substitute q (fun v => NumberedRewriteSyntax.rename (theta v) rho) := by
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => ∀ (Delta Theta : List Ty)
      (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta) (rho : Renaming Delta Theta),
      renameArguments (substituteArguments args theta) rho = substituteArguments args (fun v => NumberedRewriteSyntax.rename (theta v) rho))
  case var v => intros; rfl
  case lam body ih =>
    intro Delta Theta theta rho
    simp only [substitute,NumberedRewriteSyntax.rename]
    rw [ih _ _ (liftSubstitution theta) rho.lift,liftRenameSub]
  case app f a ihf iha =>
    intro Delta Theta theta rho
    exact congrArg₂ AuxTerm.app (ihf Delta Theta theta rho) (iha Delta Theta theta rho)
  case bottom => intros; rfl
  case ordinary f base ih =>
    intro Delta Theta theta rho
    exact congrArg (AuxTerm.ordinary f) (ih Delta Theta theta rho)
  case numbered k f tau base types extras ihb ihe =>
    intro Delta Theta theta rho
    exact congrArg₂ (fun b e => AuxTerm.numbered k f tau b types e)
      (ihb Delta Theta theta rho) (ihe Delta Theta theta rho)
  case nil => intros; rfl
  case cons Gamma sigma types q rest ihq ihr Delta Theta theta rho =>
    exact congrArg₂ AuxArguments.cons (ihq Delta Theta theta rho) (ihr Delta Theta theta rho)

theorem actualTermSubstituteRename : NumberedMixedBindingTargets.ActualTermSubstituteRename := by
  intro Symbol arity Gamma Delta Theta rho theta tau q
  exact substituteRename q Delta Theta rho theta

theorem actualArgumentSubstituteRename : NumberedMixedBindingTargets.ActualArgumentSubstituteRename := by
  intro Symbol arity Gamma Delta Theta rho theta types args
  induction types with
  | nil => cases args; rfl
  | cons tau types ih => cases args with
    | cons q rest => exact congrArg₂ AuxArguments.cons (substituteRename q Delta Theta rho theta) (ih rest)

theorem actualTermRenameSubstitute : NumberedMixedBindingTargets.ActualTermRenameSubstitute := by
  intro Symbol arity Gamma Delta Theta theta rho tau q
  exact renameSubstitute q Delta Theta theta rho

theorem actualArgumentRenameSubstitute : NumberedMixedBindingTargets.ActualArgumentRenameSubstitute := by
  intro Symbol arity Gamma Delta Theta theta rho types args
  induction types with
  | nil => cases args; rfl
  | cons tau types ih => cases args with
    | cons q rest => exact congrArg₂ AuxArguments.cons (renameSubstitute q Delta Theta theta rho) (ih rest)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMixedBindingProof
