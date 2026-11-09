module
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordEvaluationTargets
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalScheduledSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordEvaluation.Proof
open PolynomialGraphCompletion

theorem letterCorrect : Targets.LetterCorrect := by
  intro a t
  have hc := OriginalScheduled.Proof.sourceCountCorrect a.2.1 a.2.2.1 t
  simp only [letter, letterValue, rawQuadraticShift,
    KernelSourceCompletion.UniformCompletion.sourceSignedValue,
    KernelSourceCompletion.UniformCompletion.sourceSignedDepth, hc]

theorem letterDomainCorrect : Targets.LetterDomainCorrect := by
  intro a t
  have hc := OriginalScheduled.Proof.sourceCountCorrect a.2.1 a.2.2.1 t
  simp only [letterDomain, LetterDomain,
    KernelSourceCompletion.UniformCompletion.sourceSignedDepth, hc]
  split_ifs <;> simp

theorem wordCorrect : Targets.WordCorrect := by
  intro w
  induction w with
  | nil => intro t; rfl
  | cons a w ih =>
      intro t
      change word w (letter a t) = wordValue w (letterValue a t)
      rw [letterCorrect a t]
      exact ih (letterValue a t)

theorem wordDomainCorrect : Targets.WordDomainCorrect := by
  intro w
  induction w with
  | nil => intro t; simp [wordDomain, WordDomain]
  | cons a w ih =>
      intro t
      change ((letterDomain a t && wordDomain w (letter a t)) = true) ↔
        LetterDomain a t ∧ WordDomain w (letterValue a t)
      rw [Bool.and_eq_true, letterDomainCorrect a t, ih (letter a t), letterCorrect a t]

end LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordEvaluation.Proof
