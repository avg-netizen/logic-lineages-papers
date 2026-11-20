import LogicLineages.PersistentMarking.NativeClosedApplication

namespace LogicLineages.PersistentMarking.NativeClosedBetaTargets
open Spine NativeReduction NativeCarrierTargets NativeIteratorStrictTargets NativeClosedApplication

def ClosedNativeBeta : Prop :=
  ∀ S σ τ body (hl : ClosedNative S (.lam σ body) (.arrow σ τ))
    (a : ClosedNativeTerm S σ),
    let start := applyClosed ⟨.lam σ body, hl⟩ a
    ∃ result : ClosedNativeTerm S τ,
      result.val = substitute (.cons a.val .nil) 0 body ∧
      Reduction S start.val result.val ∧ NativeBelow result start

end LogicLineages.PersistentMarking.NativeClosedBetaTargets
