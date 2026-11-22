module
public import LogicLineages.PermittedControl.MixedNamedResidueRowTargets
import LogicLineages.PermittedControl.MixedNamedResidueRowFormulaProof
import LogicLineages.PermittedControl.MixedSameRankResidueStatementChecks
import Mathlib.Data.Int.ModEq

@[expose] public section
namespace LogicLineages.PermittedControl.MixedNamedResidueRow
open StatementChecks (fixed_mixedSameRankResidueActual)

theorem actualNamedRow : ActualNamedRow := by
  intro f B hf m rank c terms ρ hm typed tail
  obtain ⟨values, reads, residues⟩ :=
    fixed_mixedSameRankResidueActual f B hf m rank c terms ρ hm typed tail
  refine ⟨values, reads, ?_⟩
  intro ν hν
  exact (rowAt m (ρ rank) hm c terms ν hν).trans residues.dvd_iff.symm

end LogicLineages.PermittedControl.MixedNamedResidueRow
