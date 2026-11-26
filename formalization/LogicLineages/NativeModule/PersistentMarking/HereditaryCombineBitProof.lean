module

public import LogicLineages.NativeModule.PersistentMarking.HereditaryLatticeTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.HereditaryCombineBitProof
open HereditaryDomainCode

def number (b : Bool) : Nat := if b then 1 else 0

theorem minBits (a b : Bool) : Nat.min (number a) (number b) = number (a && b) := by
  cases a <;> cases b <;> rfl

theorem maxBits (a b : Bool) : Nat.max (number a) (number b) = number (a || b) := by
  cases a <;> cases b <;> rfl

theorem folds (xs : List Bool) (b : Bool) :
    (xs.map number).foldl Nat.min (number b) = number (b && xs.all id) ∧
    (xs.map number).foldl Nat.max (number b) = number (b || xs.any id) := by
  induction xs generalizing b with
  | nil => cases b <;> exact ⟨rfl,rfl⟩
  | cons a xs ih =>
    simp only [List.map_cons,List.foldl_cons,minBits,maxBits,List.all_cons,List.any_cons]
    rw [(ih (b && a)).1,(ih (b || a)).2]
    simp only [Bool.and_assoc,Bool.or_assoc,id_eq]
    trivial

theorem combine (meet : Bool) (xs : List Bool) :
    bitCombine meet (xs.map number) = number (if meet then xs.all id else xs.any id) := by
  cases meet with
  | false => simpa only [bitCombine,Bool.false_eq_true,if_false,number,Bool.false_or] using (folds xs false).2
  | true => simpa only [bitCombine,if_true,number,Bool.true_and] using (folds xs true).1

end LogicLineages.PersistentMarking.HereditaryCombineBitProof
