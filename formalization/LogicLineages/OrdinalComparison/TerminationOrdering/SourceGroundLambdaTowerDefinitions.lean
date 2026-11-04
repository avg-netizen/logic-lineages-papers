module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundContextTowerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceApplicativeLambdaSubstitutionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundLambdaTower
open Source NumberedRewriteSyntax SourceApplicativeSubstitution
/-- Exactly k leading ground-domain lambdas, then the actual applicative fragment. -/
def GroundLambdaFragment {Symbol : Type} {arity : Symbol → Nat} :
    Nat → {Gamma : List Ty} → {tau : Ty} → AuxTerm Symbol arity Gamma tau → Prop
  | 0, _, _, q => ApplicativeFragment q
  | k + 1, _, _, .lam (sigma := sigma) body => sigma = .ground ∧ GroundLambdaFragment k body
  | _ + 1, _, _, _ => False
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceGroundLambdaTower
