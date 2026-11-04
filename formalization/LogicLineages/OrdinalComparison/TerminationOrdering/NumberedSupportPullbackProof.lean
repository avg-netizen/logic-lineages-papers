module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSupportPullbackTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSupportPullbackProof
open Source NumberedRewriteSyntax NumberedRenamingSupport

theorem liftPullback {Gamma Delta : List Ty} (rho : Renaming Gamma Delta) (Q : VariablePredicate Delta) (sigma : Ty) :
    (fun {tau} (v : Variable (sigma :: Gamma) tau) => liftPredicate Q (rho.lift v)) =
    (fun {tau} (v : Variable (sigma :: Gamma) tau) => liftPredicate (fun v => Q (rho v)) v) := by
  funext tau v
  cases v <;> rfl

theorem supportPullback {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau) : ∀ (Delta : List Ty) (rho : Renaming Gamma Delta) (Q : VariablePredicate Delta),
    supports Q (NumberedRewriteSyntax.rename q rho) ↔ supports (fun v => Q (rho v)) q := by
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => ∀ (Delta : List Ty) (rho : Renaming Gamma Delta) (Q : VariablePredicate Delta),
      supportsArguments Q (renameArguments args rho) ↔ supportsArguments (fun v => Q (rho v)) args)
  case var v => intros; exact Iff.rfl
  case lam body ih =>
    intro Delta rho Q
    change supports (liftPredicate Q) (NumberedRewriteSyntax.rename body rho.lift) ↔ supports (liftPredicate (fun v => Q (rho v))) body
    rw [ih _ rho.lift (liftPredicate Q),liftPullback]
  case app f a ihf iha => intro Delta rho Q; exact and_congr (ihf Delta rho Q) (iha Delta rho Q)
  case bottom => intros; exact Iff.rfl
  case ordinary f base ih => intro Delta rho Q; exact ih Delta rho Q
  case numbered k f tau base types extras ihb ihe => intro Delta rho Q; exact and_congr (ihb Delta rho Q) (ihe Delta rho Q)
  case nil => intros; exact Iff.rfl
  case cons Gamma sigma types q rest ihq ihr Delta rho Q => exact and_congr (ihq Delta rho Q) (ihr Delta rho Q)

theorem actualTermSupportPullback : NumberedSupportPullbackTargets.ActualTermSupportPullback := by
  intro Symbol arity Gamma Delta rho Q tau q
  exact supportPullback q Delta rho Q

theorem actualArgumentSupportPullback : NumberedSupportPullbackTargets.ActualArgumentSupportPullback := by
  intro Symbol arity Gamma Delta rho Q types args
  induction types with
  | nil => cases args; exact Iff.rfl
  | cons tau types ih => cases args with
    | cons q rest => exact and_congr (supportPullback q Delta rho Q) (ih rest)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSupportPullbackProof
