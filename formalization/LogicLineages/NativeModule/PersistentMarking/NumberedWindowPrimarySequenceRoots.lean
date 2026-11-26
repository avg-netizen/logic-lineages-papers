module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimarySequenceTermTrace

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceRoots
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimaryExchange
open NumberedWindowPrimarySequence NumberedWindowPrimarySequenceTermTrace

def ordinaryRoot {S K C f g bs cs} (hf : HeadInWindow S K f) (hg : HeadInWindow S K g)
    (he : Spine.Equivalent S f g) (e : f.result = g.result)
    (hb : BaseTyped C bs f.arguments) (hc : BaseTyped C cs g.arguments)
    (hp : bs.toList.Perm cs.toList) :
    TypedExchangeTrace S K C f.result (.ordinary f bs) (.ordinary g cs) :=
  have hR : Typed C (.ordinary g cs) f.result := e.symm ▸ Typed.ordinary hc
  termOne ⟨.ordinary ⟨hf,hg,he⟩ e hp,.ordinary hb,hR⟩

def numberedRoot {S K C f g τ k bs cs es} (hf : HeadInWindow S K f)
    (hg : HeadInWindow S K g) (he : Spine.Equivalent S f g)
    (hb : BaseTyped C bs f.arguments) (hc : BaseTyped C cs g.arguments)
    (hx : ExtrasTyped C es) (hp : bs.toList.Perm cs.toList) :
    TypedExchangeTrace S K C τ (.numbered f τ k bs es) (.numbered g τ k cs es) :=
  termOne ⟨.numbered ⟨hf,hg,he⟩ hp,.numbered hb hx,.numbered hc hx⟩

end LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceRoots
