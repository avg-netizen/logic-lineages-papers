module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BaseTermProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceProof
open CommonLayerSyntax BoundedSource

theorem literalGuard : BoundedSourceTargets.LiteralGuard := by
  intro i p t
  cases p with
  | equal a b => simp [BoundedSource.guard]
  | less a b => simp [BoundedSource.guard]
  | negative p => simp [BoundedSource.guard]
  | existsNat j p => simp [BoundedSource.guard]
  | conjunction a b =>
      cases a with
      | equal c d => simp [BoundedSource.guard]
      | negative p => simp [BoundedSource.guard]
      | conjunction c d => simp [BoundedSource.guard]
      | existsNat j p => simp [BoundedSource.guard]
      | less c d =>
          cases c with
          | numeral n => simp [BoundedSource.guard]
          | add x y => simp [BoundedSource.guard]
          | phi x => simp [BoundedSource.guard]
          | «variable» j =>
              by_cases h : i = j
              · subst j
                by_cases hi : i ∈ d.variables <;> simp_all [BoundedSource.guard]
                all_goals rintro rfl; assumption
              · simp [BoundedSource.guard, h, Ne.symm h]

theorem independent_value (i : Nat) (t : BaseTerm) (hi : i ∉ t.variables) (ν : Nat → Nat) (n : Nat) :
    t.value (Function.update ν i n) = t.value ν := by
  apply BaseTermPrograms.Proof.supportStability
  intro j hj
  have hji : j ≠ i := by intro h; subst j; exact hi hj
  exact Function.update_of_ne hji _ _

theorem exactGuardInvariance : BoundedSourceTargets.ExactGuardInvariance := by
  intro i p t hg ν n
  rcases (literalGuard i p t).mp hg with ⟨q, rfl, hi⟩
  have hv := independent_value i t hi ν n
  refine ⟨hv, ?_⟩
  intro h
  have hb := h.1
  simpa only [SourceFormula.eval, BaseTerm.value, Function.update_self, hv] using hb

theorem exactFiniteSearch : BoundedSourceTargets.ExactFiniteSearch := by
  intro i p t hg ν
  simp only [answer, hg, List.any_eq_true, List.mem_range]

theorem actualTruth : BoundedSourceTargets.ActualTruth := by
  intro p
  induction p with
  | equal a b => intro _ ν; simp [answer, SourceFormula.eval]
  | less a b => intro _ ν; simp [answer, SourceFormula.eval]
  | negative p ih =>
      intro hp ν
      have h := ih hp ν
      cases ha : answer ν p <;> simp_all [answer, SourceFormula.eval]
  | conjunction p q ihp ihq =>
      intro hp ν
      have hh := Bool.and_eq_true_iff.mp hp
      simpa only [answer, Bool.and_eq_true, SourceFormula.eval] using and_congr (ihp hh.1 ν) (ihq hh.2 ν)
  | existsNat i p ih =>
      intro hp ν
      have hh := Bool.and_eq_true_iff.mp hp
      cases hg : BoundedSource.guard i p with
      | none => simp [hg] at hh
      | some t =>
          rw [exactFiniteSearch i p t hg ν]
          change (∃ n < t.value ν, answer (Function.update ν i n) p = true) ↔
            ∃ n, p.eval (Function.update ν i n)
          constructor
          · rintro ⟨n, _, hn⟩
            exact ⟨n, (ih hh.2 _).mp hn⟩
          · rintro ⟨n, hn⟩
            exact ⟨n, (exactGuardInvariance i p t hg ν n).2 hn, (ih hh.2 _).mpr hn⟩

theorem actualDecision : BoundedSourceTargets.ActualDecision := by
  intro values p
  constructor
  · by_cases hp : test p = true
    · simp [BoundedSource.decide, hp]
    · simp [BoundedSource.decide, hp, Bool.eq_false_iff.mpr hp]
  · intro hp b
    rw [BoundedSource.decide, if_pos hp]
    have ht := actualTruth p hp (PlainParameterDecision.valuation values)
    cases ha : answer (PlainParameterDecision.valuation values) p <;> cases b <;> simp_all

theorem actualBoundedUniversal : BoundedSourceTargets.ActualBoundedUniversal := by
  classical
  intro i t p hi hp ν
  have ht : test (.negative (.existsNat i (.conjunction (.less (.variable i) t) (.negative p)))) = true := by
    simp [test, BoundedSource.guard, hi, hp]
  rw [actualTruth _ ht ν]
  simp only [SourceFormula.eval, not_exists, not_and, not_not]
  apply forall_congr'
  intro n
  rw [independent_value i t hi ν n]
  simp only [BaseTerm.value, Function.update_self]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceProof
