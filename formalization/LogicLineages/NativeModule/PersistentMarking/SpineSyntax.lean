module

public import LogicLineages.NativeModule.PersistentMarking.Syntax

@[expose] public section

namespace LogicLineages.PersistentMarking.Spine

/- Locally nameless raw annotated auxiliary terms. Bound index 0 is the
nearest lambda; free typed names are distinct from every bound index. -/
mutual
inductive Expr where
  | free (type : Ty) (name : Nat)
  | bound (type : Ty) (index : Nat)
  | lam (domain : Ty) (body : Expr)
  | head (symbol : Head) (base : Args)
  | marked (symbol : Head) (output : Ty) (base extras : Args)
inductive Args where
  | nil
  | cons (term : Expr) (tail : Args)
end

namespace Expr

def type : Expr → Ty
  | .free σ _ => σ
  | .bound σ _ => σ
  | .lam σ body => .arrow σ body.type
  | .head f _ => f.result
  | .marked _ τ _ _ => τ
end Expr
namespace Args

def length : Args → Nat
  | .nil => 0
  | .cons _ xs => 1 + length xs

def get : Args → Nat → Option Expr
  | .nil, _ => none
  | .cons x _, 0 => some x
  | .cons _ xs, n+1 => get xs n

def append : Args → Args → Args
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (append xs ys)
end Args

mutual
/-- Shift only indices free relative to the present binder depth. -/
def shift (amount cutoff : Nat) : Expr → Expr
  | .free σ x => .free σ x
  | .bound σ i => .bound σ (if i < cutoff then i else i + amount)
  | .lam σ body => .lam σ (shift amount (cutoff+1) body)
  | .head f base => .head f (shiftArgs amount cutoff base)
  | .marked f τ base extras =>
      .marked f τ (shiftArgs amount cutoff base) (shiftArgs amount cutoff extras)
def shiftArgs (amount cutoff : Nat) : Args → Args
  | .nil => .nil
  | .cons x xs => .cons (shift amount cutoff x) (shiftArgs amount cutoff xs)
end

mutual
/-- Simultaneously remove a block of outer binders at `depth`. Substitution
values are external to that block and lifted under each residual binder.
The first value replaces the nearest removed binder. -/
def substitute (values : Args) (depth : Nat) : Expr → Expr
  | .free σ x => .free σ x
  | .bound σ i =>
      if i < depth then .bound σ i else
      match values.get (i-depth) with
      | some v => shift depth 0 v
      | none => .bound σ (i-values.length)
  | .lam σ body => .lam σ (substitute values (depth+1) body)
  | .head f base => .head f (substituteArgs values depth base)
  | .marked f τ base extras =>
      .marked f τ (substituteArgs values depth base) (substituteArgs values depth extras)
def substituteArgs (values : Args) (depth : Nat) : Args → Args
  | .nil => .nil
  | .cons x xs => .cons (substitute values depth x) (substituteArgs values depth xs)
end

/-- The suffix result type is computed from the original arrow and all
remaining argument annotations, never supplied as an unconstrained output. -/
def consumeTypes : Ty → Args → Option Ty
  | σ, .nil => some σ
  | .ground, .cons _ _ => none
  | .arrow σ τ, .cons a rest =>
      if a.type = σ then consumeTypes τ rest else none

/-- Follow only original lambdas, then append the entire remaining tuple at
one original head. Never branch on the substituted value of a variable. -/
def applyAux (q : Expr) (arguments values : Args) : Option Expr :=
  match arguments with
  | .nil => some (substitute values 0 q)
  | .cons a rest =>
    match q with
    | .lam σ body =>
        if a.type = σ then applyAux body rest (.cons a values) else none
    | .head f base =>
        (consumeTypes f.result arguments).map
          (fun τ => .marked f τ (substituteArgs values 0 base) arguments)
    | .marked f σ base extras =>
        (consumeTypes σ arguments).map
          (fun τ => .marked f τ (substituteArgs values 0 base)
            ((substituteArgs values 0 extras).append arguments))
    | .free _ _ => none
    | .bound _ _ => none
termination_by arguments

/-- Empty calls return the original syntax literally. -/
def apply (q : Expr) (arguments : Args) : Option Expr :=
  match arguments with
  | .nil => some q
  | .cons _ _ => applyAux q arguments .nil

end LogicLineages.PersistentMarking.Spine
