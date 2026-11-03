module
public import LogicLineages.OrdinalComparison.TerminationOrdering.LambdaSpineActionsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ProtectedPrefix
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open OriginalSpineActions

/-- Raise an OLD free name past the finite consumed-original-binder pre. -/
def freeRename (pre Gamma : List Ty) : Renaming Gamma (pre++Gamma) :=
  match pre with
  | [] => fun v => v
  | _::rest => fun v => .there (freeRename rest Gamma v)

/-- Retain the original pre variables as literal variables, changing only
its old-free tail context. -/
def boundVariable {tau : Ty} {pre : List Ty} (Gamma : List Ty) :
    Variable pre tau → Variable (pre++Gamma) tau
  | .here => .here
  | .there v => .there (boundVariable Gamma v)

/-- Capture-avoiding substitution UNDER the retained original binders.
No consumed argument is substituted into syntax until closePrefix is used. -/
def liftFree {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (pre : List Ty) (s : MarkedSubstitution Symbol arity Gamma Delta) :
    MarkedSubstitution Symbol arity (pre++Gamma) (pre++Delta) :=
  match pre with
  | [] => s
  | _::rest => liftSubstitution (liftFree rest s)

/-- Actual consumed argument syntax, kept in a SEPARATE closing environment.
An original variable is inspected by applyOriginalWith before this map acts. -/
def closePrefix {Symbol : Type} {arity : Symbol → Nat} {Delta : List Ty} :
    {pre : List Ty} → Arguments Symbol arity Delta pre →
      MarkedSubstitution Symbol arity (pre++Delta) Delta
  | [],.nil => fun v => .var v
  | _::_,.cons a rest => extendEnvironment (closePrefix rest) a

/-- Only the consumed original pre is protected. Old free variables remain
unprotected and may use their entire assigned tuple table. -/
def mask (pre Gamma : List Ty) : Protected (pre++Gamma) :=
  match pre with
  | [] => fun _ => false
  | _::rest => LambdaSpineActions.protectExtend (mask rest Gamma)

/-- The concrete comparison target for the generalized semantic scanner:
original pre syntax is retained through the literal application call. -/
def applyFrame {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta pre : List Ty}
    {sigma : Ty} (q : MarkedTerm Symbol arity (pre++Gamma) sigma)
    (s : MarkedSubstitution Symbol arity Gamma Delta)
    (consumed : Arguments Symbol arity Delta pre) {types : List Ty} {tau : Ty}
    (args : Arguments Symbol arity Delta types) (h : sigma=arrows types tau) :
    Option (MarkedTerm Symbol arity Delta tau) :=
  applyOriginalWith (substituteTerm q (liftFree pre s)) (closePrefix consumed) args h

end LogicLineages.OrdinalComparison.TerminationOrdering.ProtectedPrefix
