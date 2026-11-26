module

public import LogicLineages.NativeModule.PersistentMarking.NativeIteratorStrictTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalWellFoundedChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeClosedStrictWellFoundedProof
open NativeIteratorStrictTargets

theorem wf : ClosedNativeStrictWellFounded := by
  intro S τ
  exact InvImage.wf Subtype.val (NumberedWindowExternalWellFoundedChecks.exact_ConfinedStrictWellFounded S)

end LogicLineages.PersistentMarking.NativeClosedStrictWellFoundedProof
