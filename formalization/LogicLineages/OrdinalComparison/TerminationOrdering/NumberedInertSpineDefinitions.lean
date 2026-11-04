module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedVariableRootProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedInertSpine
open Source NumberedRewriteSyntax

def InertSpine {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty} :
    AuxTerm Symbol arity Gamma tau → Prop
  | .bottom _ => True
  | .var _ => True
  | .app f _ => InertSpine f
  | _ => False

def inertRank {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty} :
    AuxTerm Symbol arity Gamma tau → Nat
  | .var _ => 1
  | .app f _ => inertRank f + 2
  | _ => 0

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedInertSpine
