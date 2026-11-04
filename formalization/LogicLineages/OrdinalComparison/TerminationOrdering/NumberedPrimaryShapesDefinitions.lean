module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedLambdaRootProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryShapes
open Source NumberedRewriteSyntax

def isLambda {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty} : AuxTerm Symbol arity Gamma tau → Bool
  | .lam _ => true
  | _ => false

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryShapes
