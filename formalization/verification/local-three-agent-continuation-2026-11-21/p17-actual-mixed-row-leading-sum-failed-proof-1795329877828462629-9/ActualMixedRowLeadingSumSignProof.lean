module
public import LogicLineages.PermittedControl.ActualMixedRowLeadingSumTargets
import LogicLineages.PermittedControl.ActualMixedRowLeadingSumRowProof
import LogicLineages.PermittedControl.ActualMixedRowLeadingSumCodeProof
import LogicLineages.PermittedControl.ActualMixedRowLeadingAnnotationsStatementChecks
import LogicLineages.PermittedControl.SelectedLeadingSignCutoffStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.ActualMixedRowLeadingSum
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue

theorem exactNonzeroLeadingSign : ExactNonzeroLeadingSign := by
  intro f B selected ρ zRank c terms values reads ready raw active
  obtain ⟨annotations,C,aligned,maximum,member,largest,dominates⟩ :=
    StatementChecks.fixed_largestActualMixedRowFullValue f B selected ρ zRank terms
      values reads ready raw active
  obtain ⟨equation,bound⟩ :=
    exactSignedDecomposition f B selected ρ (ρ zRank) C c terms values annotations
      aligned raw member largest dominates
  let parts := rowParts f C terms values annotations
  let R := c + actualSum terms values
  refine ⟨annotations,C,aligned,maximum,?_⟩
  change rowCutoffCode c (terms.map encodeWeighted) ≤ ρ zRank → parts.1 ≠ 0 →
    (0 < R ↔ 0 < parts.1) ∧ (R < 0 ↔ parts.1 < 0) ∧ (0 ≤ R ↔ 0 < parts.1) ∧ R ≠ 0
  intro paid nonzero
  have cutoff := exactEffectiveCutoff.2 c terms
  rw [cutoff] at paid
  exact StatementChecks.fixed_actualSelectedLeadingSign f B selected (ρ zRank) C
    (slopeBound terms) (c.natAbs + offsetBound terms) parts.1 R (c + parts.2)
    paid dominates nonzero equation bound

end LogicLineages.PermittedControl.ActualMixedRowLeadingSum
