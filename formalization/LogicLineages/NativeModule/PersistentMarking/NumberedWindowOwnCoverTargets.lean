module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowAdmissionTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticCoverBoundsTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowOwnCoverTargets
open NumberedWindowAdmissionTargets (window)
open NumberedWindowArithmeticTyCode (encodeTy)

/-- Every admitted raw term occurs in the exact original cover selected at
its own two bounds. No lexical-context or decoded-type premise is needed. -/
def ExactAdmittedOwnCover : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty) (raw : Nat),
    (NumberedWindowAdmissionAlgorithm.bits (window S K) raw).1 = true →
    ∃ vertices : List Nat,
      NumberedWindowCoverBoundsAlgorithm.cover (window S K).2 (K.map encodeTy) raw = some vertices ∧
      raw ∈ vertices

end LogicLineages.PersistentMarking.NumberedWindowOwnCoverTargets
