module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryWeakeningProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRenamingSupport
open Source NumberedRewriteSyntax

abbrev VariablePredicate (Gamma : List Ty) := ∀ {tau : Ty}, Variable Gamma tau → Prop

def liftPredicate {Gamma : List Ty} {sigma : Ty} (P : VariablePredicate Gamma) : VariablePredicate (sigma :: Gamma)
  | _, .here => True
  | _, .there v => P v

def rangePredicate {Gamma Delta : List Ty} (rho : Renaming Gamma Delta) : VariablePredicate Delta :=
  fun {tau} v => ∃ w : Variable Gamma tau, rho w = v

mutual
def supports {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (P : VariablePredicate Gamma) : AuxTerm Symbol arity Gamma tau → Prop
  | .var v => P v
  | .lam body => supports (liftPredicate P) body
  | .app f a => supports P f ∧ supports P a
  | .bottom _ => True
  | .ordinary _ base => supportsArguments P base
  | .numbered _ _ _ base _ extras => supportsArguments P base ∧ supportsArguments P extras

def supportsArguments {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (P : VariablePredicate Gamma) : AuxArguments Symbol arity Gamma types → Prop
  | .nil => True
  | .cons q rest => supports P q ∧ supportsArguments P rest
end

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRenamingSupport
