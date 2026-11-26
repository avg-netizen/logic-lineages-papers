module
public import LogicLineages.PermittedControl.MixedRankNamedResidueRowTargets
import LogicLineages.PermittedControl.MixedRankNamedResidueRowFormulaProof
import LogicLineages.PermittedControl.MixedRankResidueStatementChecks
import Mathlib.Data.Int.ModEq

@[expose] public section
namespace LogicLineages.PermittedControl.MixedRankNamedResidueRow
open StatementChecks (fixed_actualMultiRankResidue)

theorem actualNamedRow : ActualNamedRow := by
  intro f B hf m c terms ρ positive proper tail
  obtain ⟨values,reads,congruence⟩ :=
    fixed_actualMultiRankResidue f B hf m c terms ρ positive proper tail
  refine ⟨values,reads,?_⟩
  intro ν tied
  exact (rowAt m positive c terms ρ ν tied).trans congruence.dvd_iff.symm

end LogicLineages.PermittedControl.MixedRankNamedResidueRow
