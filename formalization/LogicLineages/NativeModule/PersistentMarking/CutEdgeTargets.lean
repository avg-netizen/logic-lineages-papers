module

public import LogicLineages.NativeModule.PersistentMarking.AuxiliaryTargets
public import LogicLineages.NativeModule.PersistentMarking.ExtendedMeasure

@[expose] public section

namespace LogicLineages.PersistentMarking.CutEdgeTargets
open Spine ExtendedMeasure

/-- The primary strong-induction hypothesis, not an unbounded composition law.
Only an actual right weak tree of count strictly below n may be supplied. -/
def Below (S : Signature) (n : Nat) : Prop :=
  ∀ a b c (right : ExtendedWeakTree S b c), treeSize right < n →
    Ordinary c → ExtendedWeak S a b → ExtendedWeak S a c

def WeakStrict : Prop := ∀ S n, Below S n → ∀ a b c,
  ExtendedWeak S a b → ∀ right : ExtendedStrictTree S b c,
  treeSize right < n → Ordinary c → ExtendedStrict S a c

def StrictWeak : Prop := ∀ S n, Below S n → ∀ a b c,
  ExtendedStrict S a b → ∀ right : ExtendedWeakTree S b c,
  treeSize right < n → Ordinary c → ExtendedStrict S a c

def StrictStrict : Prop := ∀ S n, Below S n → ∀ a b c,
  ExtendedStrict S a b → ∀ right : ExtendedStrictTree S b c,
  treeSize right < n → Ordinary c → ExtendedStrict S a c

def FullEdges : Prop := WeakStrict ∧ StrictWeak ∧ StrictStrict
end LogicLineages.PersistentMarking.CutEdgeTargets
