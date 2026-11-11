module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimarySubstitutionDefinitions
@[expose] public section
/-! A binder-stable class of actual typed substitutions for source06's numbered
syntax. Images are literal same-type bottom or literal variables. This does not
replace the raw rules or the finite-window/primary/quotient relations. -/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariable
open Source NumberedRewriteSyntax

/-- No compound term can be introduced at an original variable occurrence.
Different variables may have the same image; injectivity is not required. -/
def BottomOrVariable {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta) : Prop :=
  ∀ {tau : Ty} (v : Variable Gamma tau),
    theta v = .bottom tau ∨ ∃ w : Variable Delta tau, theta v = .var w

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariable
