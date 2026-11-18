import LogicLineages.PersistentMarking.TargetExtrasRootSupport
import LogicLineages.PersistentMarking.ExtendedMeasure
namespace LogicLineages.PersistentMarking.TargetExtrasResults
open Spine TargetExtrasRootSupport ExtendedMeasure

def Transform (S : Signature) (s t : Expr) : Prop := ∀ f τ base extras,
  t = .marked f τ base extras → ∀ changed, Change f base extras changed →
  ExtendedWeak S s (.marked f τ base changed)

def Result (S : Signature) : ExtendedJudgment → Prop
  | .weak s t => Transform S s t
  | _ => True

def Smaller (S : Signature) (n : Nat) : Prop :=
  ∀ j (h : ExtendedTree S j), treeSize h < n → Result S j
end LogicLineages.PersistentMarking.TargetExtrasResults
