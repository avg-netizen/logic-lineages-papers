module
public import LogicLineages.StandardControlCurrent.InactiveEliminationCleaningProof
public import LogicLineages.StandardControlCurrent.InactiveEliminationCandidateProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsSupportProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.InactiveEliminationSemanticProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion NormalForm InactiveElimination
open InactiveEliminationCleaningProof

theorem actualNormalization : InactiveEliminationTargets.ActualNormalization := by
  intro xs p i hi ν
  exact (exists_congr (fun n => (clean_eval p (Function.update ν i n)).symm)).trans
    (LinearRowsSemanticProof.actualNormalization i (clean p) (inactive_linear xs p i hi) ν)

theorem elimination : InactiveEliminationTargets.Elimination := by
  intro xs p i hi ν
  exact (LinearRowsSemanticProof.actualLinearElimination i (clean p)
    (inactive_linear xs p i hi) ν).trans
      (exists_congr (fun n => clean_eval p (Function.update ν i n)))

theorem support : InactiveEliminationTargets.Support := by
  intro p i j hj
  obtain ⟨hne,hm⟩ := (LinearRowsSupportProof.exactOutputSupport i (clean p) j).mp hj
  exact ⟨hne,clean_support p j hm⟩

theorem guardedAtom : InactiveEliminationTargets.GuardedAtom := by
  intro xs a i hi ν
  rw [elimination xs (NormalForm.guardedAtom a) i hi ν]
  apply exists_congr
  intro n
  exact and_congr
    (NormalFormSemanticProof.exactOriginalRowDomains a.row (Function.update ν i n)) Iff.rfl
end LogicLineages.StandardControlCurrent.InactiveEliminationSemanticProof
