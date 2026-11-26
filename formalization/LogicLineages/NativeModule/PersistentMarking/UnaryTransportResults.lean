module

public import LogicLineages.NativeModule.PersistentMarking.UnaryPermutationSupport

@[expose] public section

namespace LogicLineages.PersistentMarking.UnaryTransportResults
open Spine

def Unary (S : Signature) (q s : Expr) : Prop := ∀ a b τ r,
  ExtendedWeak S a b → CallTyped EmptyContext q.type (.cons a .nil) τ → CallTyped EmptyContext s.type (.cons b .nil) τ →
  apply s (.cons b .nil) = some r → ∃ p, apply q (.cons a .nil) = some p ∧ ExtendedWeak S p r

def Result (S : Signature) : ExtendedJudgment → Prop
  | .weak q s => Unary S q s
  | _ => True

def Smaller (S : Signature) (n : Nat) : Prop := ∀ j (h : ExtendedTree S j), ExtendedMeasure.treeSize h < n → Result S j
end LogicLineages.PersistentMarking.UnaryTransportResults
