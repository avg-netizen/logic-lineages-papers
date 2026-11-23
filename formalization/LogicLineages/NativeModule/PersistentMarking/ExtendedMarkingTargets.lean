module

public import LogicLineages.NativeModule.PersistentMarking.ExtendedComparison

@[expose] public section

namespace LogicLineages.PersistentMarking.ExtendedMarkingTargets
open Spine

def Forward : Prop := ∀ S s t, ExtendedWeak S s t → ExtendedWeak S (headmark s) (headmark t)
def RemoveSource : Prop := ∀ S s t, ExtendedWeak S (headmark s) t → ExtendedWeak S s t
def ReflectMarkability : Prop := ∀ S s t r, ExtendedWeak S s t → mark t = some r → ∃ q, mark s = some q

/-- All three assertions explicitly stated in the source marking-transport lemma. -/
def FullMarking : Prop := Forward ∧ RemoveSource ∧ ReflectMarkability
end LogicLineages.PersistentMarking.ExtendedMarkingTargets
