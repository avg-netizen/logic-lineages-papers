module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceApplicativeSubstitutionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceLambdaApplicativeSubstitution
open Source NumberedRewriteSyntax
/-- The original literal applicative fragment extended by arbitrary typed
lambda bodies. Ordinary and numbered constructors remain excluded. -/
def LambdaApplicativeFragment {Symbol : Type} {arity : Symbol → Nat} :
    {Gamma : List Ty} → {tau : Ty} → AuxTerm Symbol arity Gamma tau → Prop
  | _, _, .var _ => True
  | _, _, .bottom _ => True
  | _, _, .app f a => LambdaApplicativeFragment f ∧ LambdaApplicativeFragment a
  | _, _, .lam body => LambdaApplicativeFragment body
  | _, _, _ => False
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceLambdaApplicativeSubstitution
