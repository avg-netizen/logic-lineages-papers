module
public import LogicLineages.PermittedControl.ActualPaidSignedMatrixProjectionTargets
import LogicLineages.PermittedControl.ActualPaidSignedRouteReplayProof
import LogicLineages.PermittedControl.ActualSignedRouteCartesianProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualPaidSignedMatrixProjection
open ActualPaidSignedRouteReplay (SourceHolds replayMinimum exactOriginalSignedRoutesAcrossReplay)
open ActualSignedRouteCartesian (SignedRow RowHolds exactActualSignedMatrixTuples)

theorem exactMatrixMinimum : ExactMatrixMinimum := by
  intro B r top baseline rows z
  induction rows with
  | nil =>
    exact ⟨fun _ row used => False.elim (List.not_mem_nil used),fun _ => Nat.zero_le _⟩
  | cons row rows ih =>
    change max (replayMinimum B r top baseline row.source) (matrixMinimum B r top baseline rows) ≤ z ↔ _
    constructor
    · intro above other member
      rcases List.mem_cons.mp member with eq | tail
      · subst other
        exact (le_max_left _ _).trans above
      · exact (ih.mp ((le_max_right _ _).trans above)) other tail
    · intro each
      exact max_le (each row List.mem_cons_self)
        (ih.mpr (fun q used => each q (List.mem_cons_of_mem _ used)))

theorem exactActualSameHighMatrixTuples : ExactActualSameHighMatrixTuples := by
  intro f B selected r top baseline rows setup z minimum
  have individual (row : SignedRow) (member : row ∈ rows) :
      SourceHolds f (Function.update baseline top z) row.source row.test row.positive ↔
        RowHolds f baseline r top z row :=
    exactOriginalSignedRoutesAcrossReplay f B selected r top baseline row.source (setup row member) z
      ((exactMatrixMinimum B r top baseline rows z).mp minimum row member) row.test row.positive
  refine Iff.trans ?_ (exactActualSignedMatrixTuples f baseline r top z rows).2.symm
  constructor
  · intro h row used
    exact (individual row used).mp (h row used)
  · intro h row used
    exact (individual row used).mpr (h row used)

end LogicLineages.PermittedControl.ActualPaidSignedMatrixProjection
