module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveParameterDecisionTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveSourceSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainParameterDecisionCorrectnessProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainBranchProvenanceDetectionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveParameterDecisionProof
open NormalForm AdditiveParameterDecision

/-- Add the tested name as an actual original binder to recover the public
admissibility theorem's free-linearity conjunct. No private lemma is imported. -/
theorem output_linear (p : SourceFormula) (hp : AdditiveSource.test p = true) (i : Nat) :
    LinearRows.isLinear i (AdditiveSource.eliminate p) = true := by
  have h := AdditiveSourceProof.actualAdmissibility (.existsNat i p) hp
  change (QuantifiedLinear.admissible (SourceRows.translate p) &&
    QuantifiedLinear.freeLinear i (SourceRows.translate p)) = true at h
  exact (QuantifiedLinearProof.exactOutputLinearity (SourceRows.translate p) i).trans
    (Bool.and_eq_true_iff.mp h).2

theorem pureOutputOccurrences : AdditiveParameterDecisionTargets.PureOutputOccurrences := by
  intro p hp s hs
  exact ⟨s.name, (LinearBlockProof.isLinear_iff_occurrences s.name (AdditiveSource.eliminate p)).mp
    (output_linear p hp s.name) s hs rfl⟩

theorem output_plain (p : SourceFormula) (hp : AdditiveSource.test p = true) :
    MaximalPlainBranch.isPlain (AdditiveSource.eliminate p) = true := by
  apply (PlainBranchProvenanceProof.exactPlainDetection (AdditiveSource.eliminate p)).mpr
  intro s hs
  obtain ⟨i, hi⟩ := pureOutputOccurrences p hp s hs
  rw [hi]
  rfl

theorem exactDecisionDomain : AdditiveParameterDecisionTargets.ExactDecisionDomain := by
  intro values p
  by_cases hp : AdditiveSource.test p = true
  · rw [AdditiveParameterDecision.decide, if_pos hp,
      (PlainParameterDecisionProof.exactDecisionDomains [] values (AdditiveSource.eliminate p)).1,
      output_plain p hp, hp]
  · simp [AdditiveParameterDecision.decide, hp, Bool.eq_false_iff.mpr hp]

theorem actualDecision : AdditiveParameterDecisionTargets.ActualDecision := by
  intro values p hp b
  rw [AdditiveParameterDecision.decide, if_pos hp]
  have h := (PlainParameterDecisionProof.actualDecisions [] values (AdditiveSource.eliminate p)
    (output_plain p hp) b).1
  change (_ = some b ↔ ((AdditiveSource.eliminate p).eval (PlainParameterDecision.valuation values) ↔ b = true)) at h
  rw [AdditiveSourceProof.actualQuantifierElimination p hp (PlainParameterDecision.valuation values)] at h
  exact h

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveParameterDecisionProof
