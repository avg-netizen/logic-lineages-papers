module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmTargets
open PolynomialGraphCompletion WordLinearDecisionCompletion Algorithm

/-- Every literal generated branch has valid source syntax. Every actual
nonterminal row strictly decreases the intrinsic top-level histogram; this is
not a supplied metadata or assumed local decrease field. -/
def IntrinsicStageSyntaxAndDecrease : Prop :=
  ∀ D maximum r, 3 ≤ D → RowAllowed D r → ∀ b ∈ stage D maximum r,
    BranchSyntax D maximum (rowVariables r) b ∧
      match b.action with
      | .finish _ => True
      | .descend next => RowLess D next r

/-- The actual stage exhausts original valuations, derives all original and
generated domains, and preserves exact row value at every descending branch.
Finished cases provide their actual strict sign or exact linear replacement. -/
def ExactStageSemantics : Prop :=
  ∀ D maximum r, 3 ≤ D → RowAllowed D r → ∀ ν,
    Region (stageCutoff D maximum r) maximum (rowVariables r) ν →
    RowDomain r ν ∧
    (∀ b ∈ stage D maximum r, BranchDomains b ν) ∧
    (∃ b ∈ stage D maximum r, Formula.eval ν b.guard) ∧
    ∀ b ∈ stage D maximum r, BranchCorrect maximum r b ν

/-- Exact finite emitted syntax, including every guard and residual row, is
computed uniformly from the original numeric source data. -/
def ActualStageProgram : Prop :=
  Computable (fun input : Nat × Nat × Row =>
    (stage input.1 input.2.1 input.2.2).map encodeBranch)

def ExactFiniteRankedStage : Prop :=
  IntrinsicStageSyntaxAndDecrease ∧ ExactStageSemantics ∧ ActualStageProgram

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmTargets
