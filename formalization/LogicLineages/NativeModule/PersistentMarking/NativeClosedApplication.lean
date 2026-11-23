module

public import LogicLineages.NativeModule.PersistentMarking.NativeIteratorStrictTargets
public import LogicLineages.NativeModule.PersistentMarking.NativeClosedProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeClosedApplication
open NativeIteratorStrictTargets

/-- The paper's ordinary application on actual closed native terms. -/
def applyClosed {S σ τ} (f : ClosedNativeTerm S (.arrow σ τ)) (a : ClosedNativeTerm S σ) :
    ClosedNativeTerm S τ :=
  ⟨NativeReduction.app σ τ f.val a.val,
    NativeClosedProof.application S σ τ f.val a.val f.property a.property⟩

end LogicLineages.PersistentMarking.NativeClosedApplication
