module

public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorOperatorTargets
public import LogicLineages.NativeModule.PersistentMarking.MarkedFamilyBoundsProof

@[expose] public section

namespace LogicLineages.PersistentMarking.MarkedConstructorIterationProof
open Spine FiniteDomainSchema HereditaryDomainCode
open MarkedConstructorOperator
open MarkedConstructorOperatorTargets (Endomap Monotone)

theorem retained (S : Signature) (E : Environment) (heads : List Head)
    (he : Endomap S E heads) (n : Nat) :
    iterate S E heads n ∈ MarkedFamilyCoherence.retained E heads := by
  induction n with
  | zero =>
    exact (MarkedFamilyBoundsProof.join E heads [] (by simp)).1
  | succ n ih =>
    exact (he (iterate S E heads n) ih).2.1

theorem ascending (S : Signature) (E : Environment) (heads : List Head)
    (he : Endomap S E heads) (hm : Monotone S E heads) (n : Nat) :
    MarkedFamilyLattice.le E heads (iterate S E heads n) (iterate S E heads (n+1)) = true := by
  induction n with
  | zero =>
    exact (MarkedFamilyBoundsProof.join E heads [] (by simp)).2.2 _ (retained S E heads he 1) (by simp)
  | succ n ih =>
    exact hm _ _ (retained S E heads he n) (retained S E heads he (n+1)) ih

theorem ordered (S : Signature) (E : Environment) (heads : List Head)
    (he : Endomap S E heads) (hm : Monotone S E heads) (m n : Nat) (hle : m ≤ n) :
    MarkedFamilyLattice.le E heads (iterate S E heads m) (iterate S E heads n) = true := by
  induction hle with
  | refl =>
    exact (MarkedFamilyOrderProof.partialOrder E heads).1 _ (retained S E heads he m)
  | @step n _ ih =>
    exact (MarkedFamilyOrderProof.partialOrder E heads).2.1 _ _ _
      (retained S E heads he m) (retained S E heads he n) (retained S E heads he (n+1))
      ih (ascending S E heads he hm n)

theorem constantAfter (S : Signature) (E : Environment) (heads : List Head)
    (n : Nat) (h : step S E heads (iterate S E heads n) = iterate S E heads n)
    (m : Nat) (hle : n ≤ m) : iterate S E heads m = iterate S E heads n := by
  induction hle with
  | refl => rfl
  | step _ ih =>
    rw [iterate,ih]
    exact h

theorem fixedBelow (S : Signature) (E : Environment) (heads : List Head)
    (he : Endomap S E heads) (hm : Monotone S E heads)
    (M : Code) (hM : M ∈ MarkedFamilyCoherence.retained E heads) (hfix : step S E heads M = M) (n : Nat) :
    MarkedFamilyLattice.le E heads (iterate S E heads n) M = true := by
  induction n with
  | zero =>
    exact (MarkedFamilyBoundsProof.join E heads [] (by simp)).2.2 M hM (by simp)
  | succ n ih =>
    have h := hm _ M (retained S E heads he n) hM ih
    rw [hfix] at h
    exact h

end LogicLineages.PersistentMarking.MarkedConstructorIterationProof
