module
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Separable
public meta import LogicLineages.Audit
public section
namespace LogicLineages.CartierObserverCurrent.PeriodOddRoot
open Polynomial

/-- In an algebraically closed field, a primitive root of every order that
is nonzero in the field. Elementary route: `X^q - 1` is separable and
splits, so it has `q` distinct roots; the roots of unity form a cyclic
group of that order. No cyclotomic extension theory is imported. -/
theorem primitiveRootOfNeZero (K : Type) [Field K] [IsAlgClosed K] (q : Nat)
    (hq : ((q : Nat) : K) ≠ 0) : ∃ z : K, IsPrimitiveRoot z q := by
  classical
  have hpos : q ≠ 0 := by
    rintro rfl
    exact hq Nat.cast_zero
  haveI : NeZero q := ⟨hpos⟩
  have hsep : (X ^ q - C (1 : K) : K[X]).Separable := separable_X_pow_sub_C 1 hq one_ne_zero
  have hnodup : (nthRoots q (1 : K)).Nodup := nodup_roots hsep
  have hcard : Multiset.card (nthRoots q (1 : K)) = q := by
    have hs := (IsAlgClosed.splits (X ^ q - C (1 : K) : K[X])).natDegree_eq_card_roots
    rw [natDegree_X_pow_sub_C] at hs
    exact hs.symm
  have hcount : Fintype.card (rootsOfUnity q K) = q := by
    calc
      Fintype.card (rootsOfUnity q K) = Fintype.card { x // x ∈ nthRoots q (1 : K) } :=
        Fintype.card_congr (rootsOfUnityEquivNthRoots K q)
      _ = Multiset.card (nthRoots q (1 : K)).attach := by
        change Multiset.card ((nthRoots q (1 : K)).attach.dedup) = _
        rw [Multiset.dedup_eq_self.mpr (Multiset.nodup_attach.mpr hnodup)]
      _ = Multiset.card (nthRoots q (1 : K)) := Multiset.card_attach
      _ = q := hcard
  exact card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot.mp hcount

/-- Primitive roots of every odd order in the algebraic closure of F2. -/
theorem oddPrimitiveRoot (q : Nat) (hq : Odd q) :
    ∃ z : AlgebraicClosure (ZMod 2), IsPrimitiveRoot z q := by
  apply primitiveRootOfNeZero (AlgebraicClosure (ZMod 2)) q
  rw [← map_natCast (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2))) q,
    ZMod.natCast_eq_one_iff_odd.mpr hq, map_one]
  exact one_ne_zero

#audit_namespace LogicLineages.CartierObserverCurrent.PeriodOddRoot
end LogicLineages.CartierObserverCurrent.PeriodOddRoot
