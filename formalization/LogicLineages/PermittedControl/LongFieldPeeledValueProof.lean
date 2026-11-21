module
public import LogicLineages.PermittedControl.LongFieldEffectiveTailTargets
import LogicLineages.PermittedControl.FieldComparisonPeelProof
import LogicLineages.OrdinalComparison.OrdinalRepresentationSound

@[expose] public section
namespace LogicLineages.PermittedControl.FieldComparison
open OrdinalComparison

/-- Actual old entry-peeling argument at the new exposed literal bound.
This does not unfold or alter the owner comparison proof's private body. -/
theorem long_peeled_value (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B) (a : Nat)
    (lam mu : NONote) (hL : LongField (.entry a lam mu)) (c x : Nat)
    (hx : longFieldPeelBound B lam mu c ≤ x) :
    ∃ i : Nat, FirstEntry f (countInitial lam.1.repr x) (mu + omegaMultiple c).1.repr i ∧
      x ≤ entryNormAt f (countInitial lam.1.repr x) i ∧
      FieldValue f (.entry a lam mu) x (f^[a + c] (entryNormAt f (countInitial lam.1.repr x) i)) := by
  obtain ⟨hll,hmu,hml,hlong⟩ := hL
  have hlamE := normalRepresentationSound lam
  have hlt := long_peel_bound lam.1.repr mu.1.repr (hml.trans hlamE) hmu hll hml hlong c
  obtain ⟨i,k,hi,hk,hnorm,hxe⟩ := entry_peel f B hf lam.1.repr mu.1.repr c x hlamE hll hmu hlt hx
  refine ⟨i,?_,hxe,k,hk,?_⟩
  · rw [peeled_repr]
    exact hi
  · rw [hnorm,Function.iterate_add_apply]

end LogicLineages.PermittedControl.FieldComparison
