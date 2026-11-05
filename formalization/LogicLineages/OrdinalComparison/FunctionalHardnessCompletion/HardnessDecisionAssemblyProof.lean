module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.HardnessDecisionProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SystemUndecidabilityProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.FiniteQueryCodeReductionProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededQueryCodeReductionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.HardnessDecision.Proof

/-- Strict and weak finite-query reductions each contradict the actual
finite-polynomial-system undecidability theorem separately. -/
theorem levelTwoUndecidability : Targets.LevelTwoUndecidability := by
  constructor
  · intro h
    exact SystemUndecidability.Proof.polynomialSystemUndecidable
      (finiteQueryPullback true FiniteQueryCode.Proof.existingReductions.1 h)
  · intro h
    exact SystemUndecidability.Proof.polynomialSystemUndecidable
      (finiteQueryPullback false FiniteQueryCode.Proof.existingReductions.2 h)

/-- The unchanged paper-level conjunction: both level-two undecidability
claims, both finite-query reductions, and both actual level-three single-query
reductions, all on the printed broad source domain. -/
theorem fullFunctionalHardness : HardnessTargets.FullFunctionalHardness :=
  ⟨levelTwoUndecidability.1,levelTwoUndecidability.2,
    FiniteQueryCode.Proof.existingReductions.1,FiniteQueryCode.Proof.existingReductions.2,
    SeededQueryCode.Proof.existingReductions.1,SeededQueryCode.Proof.existingReductions.2⟩

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.HardnessDecision.Proof
