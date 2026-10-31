module
public import LogicLineages.OrdinalComparison.WWDefaultSyntaxAbstractionTargets
public import LogicLineages.OrdinalComparison.WWDefaultPolicyProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxAbstractionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntax

theorem defaultPolicyAbstractionEquality : Targets.DefaultPolicyAbstractionEquality := by
  intro Γ σ m h
  unfold AdmissibleAssignment.abstraction
  simp only [defaultPolicyPartialEquality Γ σ,
    defaultPolicyRepeatEquality Γ .scalarRepeat (by decide), defaultPolicyPositiveAggregation]
  rfl

theorem defaultSyntaxPartialCorrect : Targets.DefaultSyntaxPartialCorrect := by
  intro Γ σ i t
  rw [defaultPolicyPartialEquality Γ σ i t]
  exact ordinalSyntaxPartialCorrect Γ σ i t

theorem defaultSyntaxAbstractionCorrect : Targets.DefaultSyntaxAbstractionCorrect := by
  intro Γ σ m h
  rw [defaultPolicyAbstractionEquality Γ σ m h]
  exact ordinalSyntaxAbstractionCorrect Γ σ m h
end LogicLineages.OrdinalComparison.Source.OrdinalSyntax
