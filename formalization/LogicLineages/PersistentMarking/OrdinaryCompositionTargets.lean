import LogicLineages.PersistentMarking.Comparison
namespace LogicLineages.PersistentMarking.OrdinaryCompositionTargets
open Spine

def WeakWeak : Prop := ∀ S s t u, Ordinary s → Ordinary t → Ordinary u →
  Weak S s t → Weak S t u → Weak S s u

def WeakStrict : Prop := ∀ S s t u, Ordinary s → Ordinary t → Ordinary u →
  Weak S s t → Strict S t u → Strict S s u

def StrictWeak : Prop := ∀ S s t u, Ordinary s → Ordinary t → Ordinary u →
  Strict S s t → Weak S t u → Strict S s u

def StrictStrict : Prop := ∀ S s t u, Ordinary s → Ordinary t → Ordinary u →
  Strict S s t → Strict S t u → Strict S s u

def FullComposition : Prop := WeakWeak ∧ WeakStrict ∧ StrictWeak ∧ StrictStrict
end LogicLineages.PersistentMarking.OrdinaryCompositionTargets
