module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteReductionDefinitions
@[expose] public section
/-! Number of all literal auxiliary variable occurrences, including occurrences
bound by lambdas. This is a structural rank on the original syntax, not a
replacement reduction relation or a choice of enlarged type window. -/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedVariableCount
open Source NumberedRewriteSyntax NumberedRewriteReduction

mutual
def variableCount {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau) : Nat :=
  match q with
  | .var _ => 1
  | .lam body => variableCount body
  | .app f a => variableCount f + variableCount a
  | .bottom _ => 0
  | .ordinary _ base => argumentVariableCount base
  | .numbered _ _ _ base _ extras => argumentVariableCount base + argumentVariableCount extras
def argumentVariableCount {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (args : AuxArguments Symbol arity Gamma types) : Nat :=
  match args with
  | .nil => 0
  | .cons q rest => variableCount q + argumentVariableCount rest
end

def packedVariableCount {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (q : Packed Symbol arity Gamma) : Nat := variableCount q.2

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedVariableCount
