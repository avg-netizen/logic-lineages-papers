module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierTerminationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierProof
open NormalForm PlainFrontier

theorem initial_plain (p : Formula) (hp : MaximalPlainBranch.isPlain p = true) : Plain (initial p) := by
  intro q hq
  have he : q = p := List.mem_singleton.mp hq
  subst q
  exact hp

theorem actualDecision : PlainFrontierTargets.ActualDecision := by
  intro p hp
  have hiter := actualIteration (fuel p) (initial p) (initial_plain p hp)
  constructor
  · intro hanswer
    have hm : Meaning (initial p) := hiter.mp (Or.inl hanswer)
    rcases hm with hfalse | ⟨q, hq, hsat⟩
    · cases hfalse
    · have he : q = p := List.mem_singleton.mp hq
      subst q
      exact hsat
  · intro hsat
    have hm : Meaning (run (fuel p) (initial p)) := hiter.mpr (Or.inr ⟨p, List.mem_singleton.mpr rfl, hsat⟩)
    rcases hm with hanswer | ⟨q, hq, _⟩
    · exact hanswer
    · rw [frontierExhaustion p] at hq
      cases hq

theorem exactRejectingDecision : PlainFrontierTargets.ExactRejectingDecision := by
  constructor
  · intro p
    cases h : MaximalPlainBranch.isPlain p <;> simp [PlainFrontier.decide, h]
  · intro p hp b
    simp only [PlainFrontier.decide, hp, if_true, Option.some.injEq]
    rw [Bool.eq_iff_iff, actualDecision p hp]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierProof
