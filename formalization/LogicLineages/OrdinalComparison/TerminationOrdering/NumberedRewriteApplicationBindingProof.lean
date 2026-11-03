module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteApplicationTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteApplicationBindingProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedRewriteApplication

theorem bindingRetraction : NumberedRewriteApplicationTargets.ActualBindingRetraction := by
  intro Symbol arity Gamma Delta rho sigma H tau q
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types values => ∀ (Delta : List Ty) (rho : Renaming Gamma Delta)
      (sigma : NumberedRewriteSyntax.Substitution Symbol arity Delta Gamma),
      (∀ (upsilon : Ty) (v : Variable Gamma upsilon),sigma (rho v)=AuxTerm.var v) →
      NumberedRewriteSyntax.substituteArguments (NumberedRewriteSyntax.renameArguments values rho) sigma=values)
    generalizing Delta
  case var v => exact H _ v
  case lam body ih =>
    apply congrArg AuxTerm.lam
    apply ih _ rho.lift (NumberedRewriteSyntax.liftSubstitution sigma)
    intro upsilon v
    cases v with
    | here => rfl
    | there v =>
      change NumberedRewriteSyntax.rename (sigma (rho v)) (Renaming.weaken _ _)=AuxTerm.var (.there v)
      rw [H _ v]
      rfl
  case app f a ihf iha => exact congrArg₂ AuxTerm.app (ihf Delta rho sigma H) (iha Delta rho sigma H)
  case bottom => rfl
  case ordinary f base ih => exact congrArg (AuxTerm.ordinary f) (ih Delta rho sigma H)
  case numbered n f output base types extras ihb ihe =>
    exact congrArg₂ (fun b e => AuxTerm.numbered n f output b types e) (ihb Delta rho sigma H) (ihe Delta rho sigma H)
  case nil => intros; rfl
  case cons q rest ihq ihr Delta rho sigma H =>
    exact congrArg₂ AuxArguments.cons (ihq Delta rho sigma H) (ihr Delta rho sigma H)

theorem weakeningCancellation : NumberedRewriteApplicationTargets.ActualWeakeningCancellation := by
  intro Symbol arity Gamma sigma tau q a
  exact bindingRetraction Symbol arity Gamma (sigma::Gamma) (Renaming.weaken Gamma sigma)
    (singleSubstitution a) (fun _ _ => rfl) tau q

theorem weakeningArguments {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (sigma : Ty) (values : AuxArguments Symbol arity Gamma types) (a : AuxTerm Symbol arity Gamma sigma) :
    NumberedRewriteSyntax.substituteArguments
      (NumberedRewriteSyntax.renameArguments values (Renaming.weaken Gamma sigma)) (singleSubstitution a)=values := by
  induction types with
  | nil => cases values; rfl
  | cons tau types ih => cases values with
    | cons q rest =>
      exact congrArg₂ AuxArguments.cons
        (weakeningCancellation Symbol arity Gamma sigma tau q a) (ih rest)

theorem substituteAppend {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta xs ys : List Ty}
    (a : AuxArguments Symbol arity Gamma xs) (b : AuxArguments Symbol arity Gamma ys)
    (rho : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta) :
    NumberedRewriteSyntax.substituteArguments (NumberedRewriteSyntax.appendArguments a b) rho=
      NumberedRewriteSyntax.appendArguments (NumberedRewriteSyntax.substituteArguments a rho)
        (NumberedRewriteSyntax.substituteArguments b rho) := by
  induction xs with
  | nil => cases a; rfl
  | cons sigma xs ih => cases a with
    | cons q rest => exact congrArg (AuxArguments.cons (NumberedRewriteSyntax.substitute q rho)) (ih rest)

theorem openedBetaBody {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (n : Nat) (sigma tau : Ty) (f : Head Symbol)
    (base : AuxArguments Symbol arity Gamma (headArguments arity f))
    (extraTypes : List Ty) (extras : AuxArguments Symbol arity Gamma extraTypes) (a : AuxTerm Symbol arity Gamma sigma) :
    NumberedRewriteSyntax.substitute (openNumbered n f sigma tau base extraTypes extras) (singleSubstitution a)=
      AuxTerm.numbered n f tau base (extraTypes++[sigma]) (NumberedRewriteSyntax.appendArguments extras (.cons a .nil)) := by
  simp only [openNumbered,NumberedRewriteSyntax.substitute]
  rw [weakeningArguments,substituteAppend,weakeningArguments]
  rfl

theorem openNumberedBeta : NumberedRewriteApplicationTargets.ActualOpenNumberedBeta := by
  intro Symbol arity above n Gamma sigma tau f base extraTypes extras a
  have hbody := openedBetaBody n sigma tau f base extraTypes extras a
  rw [←hbody]
  exact .beta _ a

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteApplicationBindingProof
