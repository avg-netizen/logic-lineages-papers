import LogicLineages.PersistentMarking.NativeClosedApplication

namespace LogicLineages.PersistentMarking.NativeClosedApplicationTargets
open NativeIteratorStrictTargets NativeClosedApplication

def LiteralNativeApplication : Prop :=
  ∀ S σ τ (f : ClosedNativeTerm S (.arrow σ τ)) (a : ClosedNativeTerm S σ),
    (applyClosed f a).val = NativeReduction.app σ τ f.val a.val

def NativeApplicationFunctionStrict : Prop :=
  ∀ S σ τ (s t : ClosedNativeTerm S (.arrow σ τ)) (a : ClosedNativeTerm S σ),
    NativeBelow t s → NativeBelow (applyClosed t a) (applyClosed s a)

end LogicLineages.PersistentMarking.NativeClosedApplicationTargets
