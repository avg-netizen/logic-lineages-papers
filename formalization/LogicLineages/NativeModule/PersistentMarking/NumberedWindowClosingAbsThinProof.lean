module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowClosingAbsThinCore
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowRealizationTypingProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowClosingAbsThinProof
open NumberedWindowFrameTargets
open NumberedWindowClosingScopeProof (belowEmpty belowPush)

theorem absBody : ClosingRecoversAbsBody := by
  intro σ x τ body n Q ht hf hr
  exact NumberedWindowClosingAbsThinCore.term (σ,x)
    (NumberedWindowRealizationTypingProof.typed hr _ _ ht) 0
    (NumberedWindowClosingFreshProof.realized (σ,x) hr hf) ⟨rfl,belowPush belowEmpty σ⟩

end LogicLineages.PersistentMarking.NumberedWindowClosingAbsThinProof
