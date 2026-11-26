module
public import LogicLineages.CartierObserverCurrent.PeriodTupleFactsTargets
public import LogicLineages.OrdinalComparison.LinkedResidueProof
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.PeriodTupleFacts
open LogicLineages.OrdinalComparison

theorem rootExists : Targets.RootExists := by
  intro u hu
  have hr := (actualLinkedResidueArithmetic u (by omega)).1
  have hc : (actualLinkedModulus u : ZMod 2) = 1 := by
    norm_num [actualLinkedModulus, Nat.cast_add, Nat.cast_pow,
      show actualLinkedHalfExponent u ≠ 0 by omega] <;> decide
  letI : NeZero (actualLinkedModulus u : ZMod 2) := ⟨by rw [hc]; exact one_ne_zero⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ActualResidueField (actualLinkedModulus u)
  exact ⟨⟨z, hz⟩⟩

theorem actualIterate : Targets.ActualIterate := by
  intro u v s z
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Function.iterate_succ_apply']
    change (((actualResidueTupleFrobenius u)^[s] v) z) ^ 2 = _
    rw [ih, ← pow_mul, ← pow_succ]

#audit_namespace LogicLineages.CartierObserverCurrent.PeriodTupleFacts
end LogicLineages.CartierObserverCurrent.PeriodTupleFacts
