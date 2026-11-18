import LogicLineages.PersistentMarking.Signature
namespace LogicLineages.PersistentMarking.NameBridge
open Spine
abbrev Name := Ty × Nat

/- Each named variable is the pair (type,name); its declared type is intrinsic.
This deliberately does not reuse the earlier Nat-only named context. -/
mutual
 inductive NamedTyped : Term → Ty → Prop where
   | var : NamedTyped (.var σ x) σ
   | lam : NamedTyped body τ → NamedTyped (.lam σ x body) (.arrow σ τ)
   | head : NamedBase base f.arguments → NamedTyped (.head f base) f.result
   | marked : NamedBase base f.arguments → NamedExtras extras →
       NamedTyped (.marked f τ base extras) τ
 inductive NamedBase : List Term → List Ty → Prop where
   | nil : NamedBase [] []
   | cons : NamedTyped q σ → NamedBase qs types → NamedBase (q::qs) (σ::types)
 inductive NamedExtras : List Term → Prop where
   | nil : NamedExtras []
   | cons : NamedTyped q σ → NamedExtras qs → NamedExtras (q::qs)
end

mutual
 def NamedValid (S : Signature) : Term → Prop
   | .var _ _ => True
   | .lam _ _ body => NamedValid S body
   | .head f base => Admitted S f ∧ NamedValidArgs S base
   | .marked f _ base extras => Admitted S f ∧ NamedValidArgs S base ∧ NamedValidArgs S extras
 def NamedValidArgs (S : Signature) : List Term → Prop
   | [] => True
   | q::qs => NamedValid S q ∧ NamedValidArgs S qs
end

def nameLookup : List Name → Name → Option Nat
  | [], _ => none
  | y::ys, x => if x = y then some 0 else (nameLookup ys x).map Nat.succ

mutual
 def encode (env : List Name) : Term → Expr
   | .var σ x => match nameLookup env (σ,x) with
       | some i => .bound σ i
       | none => .free σ x
   | .lam σ x body => .lam σ (encode ((σ,x)::env) body)
   | .head f base => .head f (encodeArgs env base)
   | .marked f τ base extras => .marked f τ (encodeArgs env base) (encodeArgs env extras)
 def encodeArgs (env : List Name) : List Term → Args
   | [] => .nil
   | q::qs => .cons (encode env q) (encodeArgs env qs)
end

mutual
 def nameOccurs (n : Name) : Term → Bool
   | .var σ x => decide (n = (σ,x))
   | .lam σ x body => decide (n = (σ,x)) || nameOccurs n body
   | .head _ base => namesOccur n base
   | .marked _ _ base extras => namesOccur n base || namesOccur n extras
 def namesOccur (n : Name) : List Term → Bool
   | [] => false
   | q::qs => nameOccurs n q || namesOccur n qs
end

/- Rename free occurrences of exactly one typed name, masking at its binder.
Used for alpha conversion only with a new name absent from every body name. -/
mutual
 def renameFree (old new : Name) : Term → Term
   | .var σ x => if (σ,x) = old then .var new.1 new.2 else .var σ x
   | .lam σ x body => if (σ,x) = old then .lam σ x body
       else .lam σ x (renameFree old new body)
   | .head f base => .head f (renameFreeArgs old new base)
   | .marked f τ base extras => .marked f τ (renameFreeArgs old new base) (renameFreeArgs old new extras)
 def renameFreeArgs (old new : Name) : List Term → List Term
   | [] => []
   | q::qs => renameFree old new q :: renameFreeArgs old new qs
end

mutual
 inductive Alpha : Term → Term → Prop where
   | refl : Alpha q q
   | symm : Alpha q r → Alpha r q
   | trans : Alpha q r → Alpha r s → Alpha q s
   | lam : Alpha q r → Alpha (.lam σ x q) (.lam σ x r)
   | head : AlphaArgs qs rs → Alpha (.head f qs) (.head f rs)
   | marked : AlphaArgs qs rs → AlphaArgs es fs →
       Alpha (.marked f τ qs es) (.marked f τ rs fs)
   | rename : nameOccurs (σ,z) body = false → z ≠ x →
       Alpha (.lam σ x body) (.lam σ z (renameFree (σ,x) (σ,z) body))
 inductive AlphaArgs : List Term → List Term → Prop where
   | nil : AlphaArgs [] []
   | cons : Alpha q r → AlphaArgs qs rs → AlphaArgs (q::qs) (r::rs)
end

mutual
 def Scoped (types : List Ty) : Expr → Prop
   | .free _ _ => True
   | .bound σ i => types[i]? = some σ
   | .lam σ body => Scoped (σ::types) body
   | .head _ base => ScopedArgs types base
   | .marked _ _ base extras => ScopedArgs types base ∧ ScopedArgs types extras
 def ScopedArgs (types : List Ty) : Args → Prop
   | .nil => True
   | .cons q qs => Scoped types q ∧ ScopedArgs types qs
end

mutual
 def maxFreeName : Expr → Nat
   | .free _ x => x
   | .bound _ _ => 0
   | .lam _ body => maxFreeName body
   | .head _ base => maxFreeArgs base
   | .marked _ _ base extras => max (maxFreeArgs base) (maxFreeArgs extras)
 def maxFreeArgs : Args → Nat
   | .nil => 0
   | .cons q qs => max (maxFreeName q) (maxFreeArgs qs)
end

def maxEnv : List Name → Nat
  | [] => 0
  | (_,x)::xs => max x (maxEnv xs)

def freshName (env : List Name) (q : Expr) : Nat := max (maxEnv env) (maxFreeName q) + 1

mutual
 def decode (env : List Name) : Expr → Term
   | .free σ x => .var σ x
   | .bound σ i => match env[i]? with
       | some (_,x) => .var σ x
       | none => .var σ 0
   | .lam σ body =>
       let x := freshName env body
       .lam σ x (decode ((σ,x)::env) body)
   | .head f base => .head f (decodeArgs env base)
   | .marked f τ base extras => .marked f τ (decodeArgs env base) (decodeArgs env extras)
 def decodeArgs (env : List Name) : Args → List Term
   | .nil => []
   | .cons q qs => decode env q :: decodeArgs env qs
end

/-- Open one actual binder using the existing capture-avoiding operation. -/
def openBody (σ : Ty) (x : Nat) (body : Expr) : Expr :=
  substitute (.cons (.free σ x) .nil) 0 body

mutual
 def freeOccurs (n : Name) : Expr → Bool
   | .free σ x => decide (n = (σ,x))
   | .bound _ _ => false
   | .lam _ body => freeOccurs n body
   | .head _ base => freeOccursArgs n base
   | .marked _ _ base extras => freeOccursArgs n base || freeOccursArgs n extras
 def freeOccursArgs (n : Name) : Args → Bool
   | .nil => false
   | .cons q qs => freeOccurs n q || freeOccursArgs n qs
end

end LogicLineages.PersistentMarking.NameBridge
