module
public import LogicLineages.CartierObserverCurrent.PeriodTupleFactsTargets
import LogicLineages.CartierObserverCurrent.PeriodOddRootProof
import LogicLineages.OrdinalComparison.LinkedResidueProof
public meta import LogicLineages.Audit
public section
namespace LogicLineages.CartierObserverCurrent.PeriodTupleFacts
open LogicLineages.OrdinalComparison

theorem actualModulusOdd (u : Nat) (hu : 5 ≤ u) : Odd (actualLinkedModulus u) := by
  have hr : 96 ≤ actualLinkedHalfExponent u := (actualLinkedResidueArithmetic u (by omega)).1
  have hne : actualLinkedHalfExponent u ≠ 0 := by omega
  rw [actualLinkedModulus.eq_1]
  exact Even.add_one (Nat.even_pow.mpr ⟨even_two, hne⟩)

theorem rootExists : Targets.RootExists := by
  intro u hu
  obtain ⟨z, hz⟩ := PeriodOddRoot.oddPrimitiveRoot (actualLinkedModulus u) (actualModulusOdd u hu)
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
