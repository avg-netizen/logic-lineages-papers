import LogicLineages.PersistentMarking.NameBridge
import LogicLineages.PersistentMarking.FreeSubstitution
namespace LogicLineages.PersistentMarking.StructuralContext
open Spine NameBridge

def closingMap (name : Name) : FreeMap := fun σ x =>
  if (σ,x) = name then .bound σ 0 else .free σ x

def close (name : Name) (q : Expr) : Expr := freeSub (closingMap name) 0 q

def openingMap (name : Name) (y : Nat) : FreeMap := fun σ x =>
  if (σ,x) = name then .free σ y else .free σ x

/- Binder names are intentional: filling may capture free names of the hole.
No freshness condition is imposed on the hole. -/
inductive Context where
  | hole
  | head (f : Head) (before : Args) (inside : Context) (after : Args)
  | bind (name : Name) (inside : Context)

def fill : Context → Expr → Expr
  | .hole, q => q
  | .head f before inside after, q => .head f (before.append (.cons (fill inside q) after))
  | .bind name inside, q => .lam name.1 (close name (fill inside q))

inductive ContextTyped (S : Signature) : Context → Ty → Ty → Prop where
  | hole : ContextTyped S .hole σ σ
  | head : ContextTyped S inside σ τ → Admitted S f →
      BaseTyped EmptyContext before beforeTypes → ValidArgs S before → OrdinaryArgs before →
      BaseTyped EmptyContext after afterTypes → ValidArgs S after → OrdinaryArgs after →
      f.arguments = beforeTypes ++ τ :: afterTypes →
      ContextTyped S (.head f before inside after) σ f.result
  | bind : ContextTyped S inside σ τ →
      ContextTyped S (.bind name inside) σ (.arrow name.1 τ)

inductive NamedContext where
  | hole
  | head (f : Head) (before : List Term) (inside : NamedContext) (after : List Term)
  | bind (name : Name) (inside : NamedContext)

def namedFill : NamedContext → Term → Term
  | .hole, q => q
  | .head f before inside after, q => .head f (before ++ namedFill inside q :: after)
  | .bind name inside, q => .lam name.1 name.2 (namedFill inside q)

def encodeContext : NamedContext → Context
  | .hole => .hole
  | .head f before inside after => .head f (encodeArgs [] before) (encodeContext inside) (encodeArgs [] after)
  | .bind name inside => .bind name (encodeContext inside)

end LogicLineages.PersistentMarking.StructuralContext
