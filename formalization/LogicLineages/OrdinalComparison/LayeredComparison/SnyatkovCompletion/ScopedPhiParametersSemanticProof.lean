module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiParametersTermProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveParameterDecisionSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiParametersProof
open CommonLayerSyntax ScopedPhiParameters

theorem scopedFormulaMeaning : ScopedPhiParametersTargets.ScopedFormulaMeaning := by
  intro bound ambient current p hp hagree
  induction p generalizing bound current with
  | equal a b =>
      have hh := Bool.and_eq_true_iff.mp hp
      change (freezeTerm ambient a).value current = (freezeTerm ambient b).value current ↔ _
      rw [scopedTermMeaning bound ambient current a hh.1 hagree,
        scopedTermMeaning bound ambient current b hh.2 hagree]
      rfl
  | less a b =>
      have hh := Bool.and_eq_true_iff.mp hp
      change (freezeTerm ambient a).value current < (freezeTerm ambient b).value current ↔ _
      rw [scopedTermMeaning bound ambient current a hh.1 hagree,
        scopedTermMeaning bound ambient current b hh.2 hagree]
      rfl
  | negative p ih => exact not_congr (ih bound current hp hagree)
  | conjunction p q ihp ihq =>
      have hh := Bool.and_eq_true_iff.mp hp
      exact and_congr (ihp bound current hh.1 hagree) (ihq bound current hh.2 hagree)
  | existsNat i p ih =>
      change (∃ n : Nat, (freezeFormula ambient p).eval (Function.update current i n)) ↔
        ∃ n : Nat, p.eval (Function.update current i n)
      apply exists_congr
      intro n
      apply ih (i :: bound) (Function.update current i n) hp
      intro j hj
      have hji : j ≠ i := by intro h; subst j; exact hj List.mem_cons_self
      have hjb : j ∉ bound := fun h => hj (List.mem_cons_of_mem _ h)
      rw [Function.update_of_ne hji]
      exact hagree j hjb

theorem exactDecisionDomain : ScopedPhiParametersTargets.ExactDecisionDomain := by
  intro values p
  by_cases hp : test [] p = true
  · rw [ScopedPhiParameters.decide, if_pos hp,
      AdditiveParameterDecisionProof.exactDecisionDomain values _,
      additiveFormulaOutput, hp]
  · simp [ScopedPhiParameters.decide, hp]

theorem actualDecision : ScopedPhiParametersTargets.ActualDecision := by
  intro values p hp b
  rw [ScopedPhiParameters.decide, if_pos hp]
  have h := AdditiveParameterDecisionProof.actualDecision values
    (freezeFormula (PlainParameterDecision.valuation values) p)
    (additiveFormulaOutput _ p) b
  rw [scopedFormulaMeaning [] _ _ p hp (fun _ _ => rfl)] at h
  exact h

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiParametersProof
