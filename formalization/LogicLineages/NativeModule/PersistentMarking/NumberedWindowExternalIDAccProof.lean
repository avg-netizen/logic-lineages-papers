module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalIDOperatorTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticDirectCodeChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowExternalIDAccProof
open NumberedWindowArithmeticAllContextTargets NumberedWindowArithmeticAllContextChecks
open NumberedWindowArithmeticDirectCodeTargets NumberedWindowArithmeticDirectCodeChecks
open NumberedWindowExternalIDOperators NumberedWindowExternalIDOperatorTargets

private theorem guardedAcc (G : Pred) (R : Nat → Nat → Prop)
    (descendantDomain : ∀ source target, R source target → G target) (n : Nat) :
    Least (guardedStep G R) n ↔ G n ∧ Acc (fun target source => R source target) n := by
  constructor
  · intro h
    let P : Pred := fun x => G x ∧ Acc (fun target source => R source target) x
    have hp : IsPrefixed (guardedStep G R) P := by
      intro x hx
      exact ⟨hx.1,Acc.intro x (fun m hm => (hx.2 m hm).2)⟩
    exact h P hp
  · rintro ⟨hn,ha⟩
    intro P hp
    revert hn
    induction ha with
    | intro x _ ih =>
      intro hx
      exact hp x ⟨hx,fun m hm => ih m hm (descendantDomain x m hm)⟩

theorem actualAcc : ActualGuardedAccessibilitySemantics := by
  intro S K n
  exact ⟨guardedAcc (AdmittedAddress S K) (AddressPositive S K)
      (fun source target h => (exact_AddressPathDomain S K source target h).2) n,
    guardedAcc (AdmittedAddressListCode S K) (DirectAtCode S K)
      (fun source target h => (exact_OriginalCodedDirectDomains S K source target h).2) n⟩

end LogicLineages.PersistentMarking.NumberedWindowExternalIDAccProof
