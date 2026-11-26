import Init

namespace LogicLineages.PersistentMarking

/-- Paper 16, §1: literal simple types, not type levels. -/
inductive Ty where
  | ground : Ty
  | arrow : Ty → Ty → Ty
  deriving DecidableEq, Repr

/-- Ranked symbols retain an explicit fixed arity. A signature interpretation
fixes which names and arities are admitted; the raw carrier does not invent
curried native symbols for these ground-ranked declarations. -/
inductive Head where
  | zero
  | succ
  | case (result : Ty)
  | recursor (result : Ty)
  | app (domain codomain : Ty)
  | ranked (name arity : Nat)
  deriving DecidableEq, Repr

namespace Head
open Ty

def result : Head → Ty
  | .zero => .ground
  | .succ => .arrow .ground .ground
  | .case τ => .arrow .ground (.arrow τ (.arrow τ τ))
  | .recursor τ => .arrow .ground
      (.arrow (.arrow .ground (.arrow τ τ)) (.arrow τ τ))
  | .app _ τ => τ
  | .ranked _ _ => .ground

def arguments : Head → List Ty
  | .app σ τ => [.arrow σ τ, σ]
  | .ranked _ n => List.replicate n .ground
  | _ => []
end Head

/-- Raw annotated presentation of the paper's auxiliary syntax. Binders use
named variables; well-typedness/alpha equivalence are separate obligations.
The laws here are equivariant in names and hold before taking that quotient. -/
inductive Term where
  | var (type : Ty) (name : Nat)
  | lam (domain : Ty) (name : Nat) (body : Term)
  | head (symbol : Head) (base : List Term)
  | marked (symbol : Head) (output : Ty) (base extras : List Term)
  deriving Repr

namespace Term

def type : Term → Ty
  | .var σ _ => σ
  | .lam σ _ body => .arrow σ body.type
  | .head f _ => f.result
  | .marked _ τ _ _ => τ

/-- Partial persistent marking, literally following the initial lambda spine.
An already marked node is fixed, including all its base and extra arguments. -/
def mark : Term → Option Term
  | .var _ _ => none
  | .lam σ x body => (mark body).map (.lam σ x)
  | .head f base => some (.marked f f.result base [])
  | .marked f τ base extras => some (.marked f τ base extras)

/-- Total top marking. No recursion enters a head's base or extra arguments. -/
def headmark : Term → Term
  | .var σ x => .var σ x
  | .lam σ x body => .lam σ x (headmark body)
  | .head f base => .marked f f.result base []
  | .marked f τ base extras => .marked f τ base extras

/-- Exactly the original lambda-spine obstruction to partial marking. -/
def variableSpine : Term → Bool
  | .var _ _ => true
  | .lam _ _ body => variableSpine body
  | _ => false

end Term
end LogicLineages.PersistentMarking
