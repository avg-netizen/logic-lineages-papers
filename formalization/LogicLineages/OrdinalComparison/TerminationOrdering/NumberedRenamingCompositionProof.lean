module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRenamingCompositionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRenamingCompositionProof
open Source NumberedRewriteSyntax

theorem liftCompose {Gamma Delta Theta : List Ty} (rho : Renaming Gamma Delta)
    (eta : Renaming Delta Theta) (sigma : Ty) :
    (fun {tau} (v : Variable (sigma::Gamma) tau) => eta.lift (rho.lift v)) =
      (fun {tau} (v : Variable (sigma::Gamma) tau) => Renaming.lift (fun v => eta (rho v)) v) := by
  funext tau v
  cases v <;> rfl

theorem renameCompose {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau) :
    ∀ (Delta Theta : List Ty) (rho : Renaming Gamma Delta) (eta : Renaming Delta Theta),
    NumberedRewriteSyntax.rename (NumberedRewriteSyntax.rename q rho) eta =
    NumberedRewriteSyntax.rename q (fun v => eta (rho v)) := by
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => ∀ (Delta Theta : List Ty)
      (rho : Renaming Gamma Delta) (eta : Renaming Delta Theta),
      renameArguments (renameArguments args rho) eta = renameArguments args (fun v => eta (rho v)))
  case var v => intros; rfl
  case lam body ih =>
    intro Delta Theta rho eta
    simp only [NumberedRewriteSyntax.rename]
    rw [ih _ _ rho.lift eta.lift, liftCompose]
  case app f a ihf iha =>
    intro Delta Theta rho eta
    exact congrArg₂ AuxTerm.app (ihf Delta Theta rho eta) (iha Delta Theta rho eta)
  case bottom => intros; rfl
  case ordinary f base ih =>
    intro Delta Theta rho eta
    exact congrArg (AuxTerm.ordinary f) (ih Delta Theta rho eta)
  case numbered k f tau base types extras ihb ihe =>
    intro Delta Theta rho eta
    exact congrArg₂ (fun b e => AuxTerm.numbered k f tau b types e)
      (ihb Delta Theta rho eta) (ihe Delta Theta rho eta)
  case nil => intros; rfl
  case cons Gamma sigma types q rest ihq ihr Delta Theta rho eta =>
    exact congrArg₂ AuxArguments.cons (ihq Delta Theta rho eta) (ihr Delta Theta rho eta)

theorem actualTermRenamingComposition : NumberedRenamingCompositionTargets.ActualTermRenamingComposition := by
  intro Symbol arity Gamma Delta Theta rho eta tau q
  exact renameCompose q Delta Theta rho eta

theorem actualArgumentRenamingComposition : NumberedRenamingCompositionTargets.ActualArgumentRenamingComposition := by
  intro Symbol arity Gamma Delta Theta rho eta types args
  induction types with
  | nil => cases args; rfl
  | cons tau types ih => cases args with
    | cons q rest => exact congrArg₂ AuxArguments.cons (renameCompose q Delta Theta rho eta) (ih rest)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRenamingCompositionProof
