module
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public meta import LogicLineages.Audit
public section
namespace LogicLineages.CartierObserverCurrent.PeriodOddRoot

/-- Primitive roots of every odd order in the algebraic closure of F2. The
modulus is a variable. The cyclotomic supplier is a private import, so no
module using this lemma loads it. -/
theorem oddPrimitiveRoot (q : Nat) (hq : Odd q) :
    ∃ z : AlgebraicClosure (ZMod 2), IsPrimitiveRoot z q := by
  haveI : NeZero ((q : Nat) : ZMod 2) :=
    ⟨by rw [ZMod.natCast_eq_one_iff_odd.mpr hq]; exact one_ne_zero⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure (ZMod 2)) q

#audit_namespace LogicLineages.CartierObserverCurrent.PeriodOddRoot
end LogicLineages.CartierObserverCurrent.PeriodOddRoot
