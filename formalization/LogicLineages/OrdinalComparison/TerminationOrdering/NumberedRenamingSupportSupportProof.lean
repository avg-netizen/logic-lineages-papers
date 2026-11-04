module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRenamingSupportTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRenamingSupportSupportProof
open Source NumberedRewriteSyntax NumberedRenamingSupport

theorem liftRange (Gamma Delta : List Ty) (rho : Renaming Gamma Delta) (sigma tau : Ty)
    (v : Variable (sigma :: Delta) tau) :
    liftPredicate (rangePredicate rho) v ↔ rangePredicate (Renaming.lift rho) v := by
  cases v with
  | here =>
    constructor
    · intro h; exact ⟨.here,rfl⟩
    · intro h; trivial
  | there v =>
    constructor
    · rintro ⟨w,hw⟩
      exact ⟨.there w,congrArg Variable.there hw⟩
    · rintro ⟨w,hw⟩
      cases w with
      | here => cases hw
      | there w => exact ⟨w,by injection hw⟩

theorem liftRangePredicate {Gamma Delta : List Ty} (rho : Renaming Gamma Delta) (sigma : Ty) :
    (fun {tau} (v : Variable (sigma :: Delta) tau) => liftPredicate (rangePredicate rho) v) =
    (fun {tau} (v : Variable (sigma :: Delta) tau) => rangePredicate (Renaming.lift rho) v) := by
  funext tau v
  exact propext (liftRange Gamma Delta rho sigma tau v)

theorem renamedSupported {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau) : ∀ (Delta : List Ty) (rho : Renaming Gamma Delta),
    supports (rangePredicate rho) (NumberedRewriteSyntax.rename q rho) := by
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => ∀ (Delta : List Ty) (rho : Renaming Gamma Delta),
      supportsArguments (rangePredicate rho) (renameArguments args rho))
  case var v => intro Delta rho; exact ⟨v,rfl⟩
  case lam body ih =>
    intro Delta rho
    change supports (liftPredicate (rangePredicate rho)) (NumberedRewriteSyntax.rename body rho.lift)
    rw [liftRangePredicate]
    exact ih _ rho.lift
  case app f a ihf iha => intro Delta rho; exact ⟨ihf Delta rho,iha Delta rho⟩
  case bottom => intros; trivial
  case ordinary f base ih => intro Delta rho; exact ih Delta rho
  case numbered k f tau base types extras ihb ihe => intro Delta rho; exact ⟨ihb Delta rho,ihe Delta rho⟩
  case nil => intros; trivial
  case cons Gamma sigma types q rest ihq ihr Delta rho => exact ⟨ihq Delta rho,ihr Delta rho⟩

theorem renamedArgumentsSupported {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {types : List Ty}
    (args : AuxArguments Symbol arity Gamma types) (Delta : List Ty) (rho : Renaming Gamma Delta) :
    supportsArguments (rangePredicate rho) (renameArguments args rho) := by
  induction types with
  | nil => cases args; trivial
  | cons tau types ih => cases args with
    | cons q rest => exact ⟨renamedSupported q Delta rho,ih rest⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRenamingSupportSupportProof
