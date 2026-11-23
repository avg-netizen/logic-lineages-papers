module

public import LogicLineages.NativeModule.PersistentMarking.NativeIteratorTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeIteratorStrictTargets
open Spine NativeCarrierTargets NativeIndexedCarrierTargets NativeIteratorTargets

def ClosedNativeTerm (S : Signature) (τ : Ty) := {q : Expr // ClosedNative S q τ}

def NativeBelow {S τ} (target source : ClosedNativeTerm S τ) : Prop :=
  ConfinedPair.Strict S source.val target.val

def ClosedNativeStrictWellFounded : Prop :=
  ∀ S τ, WellFounded (@NativeBelow S τ)

/-- Both beta midpoints lie in the same literal closed native type as
the applied iterator and its original indexed carrier. -/
def IteratorNativeStrictChain : Prop :=
  ∀ S A i p u, ClosedNative S i indexType → ClosedNative S p (functionType A) →
    ClosedNative S u (actualType A) →
    ∃ (start afterI afterP final : ClosedNativeTerm S (actualType A)),
      start.val = applied A i p u ∧ afterI.val = afterIndex A i p u ∧
      afterP.val = afterFunction A i p u ∧ final.val = indexedW A p u i ∧
      NativeBelow afterI start ∧ NativeBelow afterP afterI ∧ NativeBelow final afterP

end LogicLineages.PersistentMarking.NativeIteratorStrictTargets
