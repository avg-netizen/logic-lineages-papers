module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomAccessibilityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomSpine
open Source NumberedRewriteSyntax

def BottomSpine {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty} :
    AuxTerm Symbol arity Gamma tau → Prop
  | .bottom _ => True
  | .app f _ => BottomSpine f
  | _ => False

def spineDepth {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty} :
    AuxTerm Symbol arity Gamma tau → Nat
  | .app f _ => spineDepth f + 1
  | _ => 0

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomSpine
