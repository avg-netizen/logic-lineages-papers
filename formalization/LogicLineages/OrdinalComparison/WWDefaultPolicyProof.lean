module
public import LogicLineages.OrdinalComparison.WWDefaultPolicyTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntax

theorem defaultPolicyPartialEquality : Targets.DefaultPolicyPartialEquality := by
  intro Γ σ i t
  induction t generalizing i with
  | var c => rfl
  | zero => rfl
  | one => rfl
  | omega => rfl
  | add a b iha ihb =>
    conv_lhs => rw [AdmissiblePartial.run.eq_def]
    conv_rhs => rw [AdmissiblePartial.run.eq_def]
    simp only [iha, ihb]
    rfl
  | emul a b iha ihb =>
    conv_lhs => rw [AdmissiblePartial.run.eq_def]
    conv_rhs => rw [AdmissiblePartial.run.eq_def]
    simp only [iha, ihb]
    rfl
  | collapse a b iha ihb =>
    conv_lhs => rw [AdmissiblePartial.run.eq_def]
    conv_rhs => rw [AdmissiblePartial.run.eq_def]
    simp only [iha, ihb]

theorem defaultPolicyRepeatEquality : Targets.DefaultPolicyRepeatEquality := by
  intro Γ site hsite count t
  cases site <;> cases count <;> simp_all [AdmissibleAssignment.repeated, defaultPolicy, defaultShape, allLeftPolicy]

theorem defaultPolicyPositiveAggregation : Targets.DefaultPolicyPositiveAggregation := by
  intro n
  rfl

theorem defaultPolicyBoxTail : Targets.DefaultPolicyBoxTail := by
  intro Γ n f g
  unfold AdmissibleAssignment.boxTail
  by_cases hn : n=0
  · simp [hn]
  · rw [if_neg hn, if_neg hn]
    rfl
end LogicLineages.OrdinalComparison.Source.OrdinalSyntax
