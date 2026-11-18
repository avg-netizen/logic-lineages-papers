import LogicLineages.PersistentMarking.SpineTyping
namespace LogicLineages.PersistentMarking.Spine

/-- Ordered finite ranked declarations, lowest precedence first. Names have
one fixed arity. Native and application heads are different constructors. -/
structure Signature where
  entries : List (Nat × Nat)
  uniqueNames : ∀ (i j name a b : Nat),
    entries[i]? = some (name,a) → entries[j]? = some (name,b) → i = j

/-- Return declared arity and actual table position. -/
def lookupRank : List (Nat × Nat) → Nat → Option (Nat × Nat)
  | [], _ => none
  | (name,arity)::rest, x =>
      if x = name then some (arity,0)
      else (lookupRank rest x).map (fun p => (p.1,p.2+1))

def classRank (S : Signature) : Head → Option Nat
  | .app _ _ => some 0
  | .zero | .succ | .case _ | .recursor _ => some 1
  | .ranked name arity =>
    match lookupRank S.entries name with
    | none => none
    | some (a,i) => if arity = a then some (i+2) else none

def Admitted (S : Signature) (f : Head) : Prop := ∃ n, classRank S f = some n

def Equivalent (S : Signature) (f g : Head) : Prop :=
  ∃ n, classRank S f = some n ∧ classRank S g = some n

def Precedes (S : Signature) (f g : Head) : Prop :=
  ∃ m n, classRank S f = some m ∧ classRank S g = some n ∧ n < m

mutual
 def Valid (S : Signature) : Expr → Prop
   | .free _ _ | .bound _ _ => True
   | .lam _ body => Valid S body
   | .head f base => Admitted S f ∧ ValidArgs S base
   | .marked f _ base extras => Admitted S f ∧ ValidArgs S base ∧ ValidArgs S extras
 def ValidArgs (S : Signature) : Args → Prop
   | .nil => True
   | .cons q qs => Valid S q ∧ ValidArgs S qs
end

mutual
 def Ordinary : Expr → Prop
   | .free _ _ | .bound _ _ => True
   | .lam _ body => Ordinary body
   | .head _ base => OrdinaryArgs base
   | .marked _ _ _ _ => False
 def OrdinaryArgs : Args → Prop
   | .nil => True
   | .cons q qs => Ordinary q ∧ OrdinaryArgs qs
end

abbrev EmptyContext : BoundContext := fun _ => none

def PaperTerm (S : Signature) (q : Expr) (σ : Ty) : Prop :=
  Typed EmptyContext q σ ∧ Valid S q

end LogicLineages.PersistentMarking.Spine
