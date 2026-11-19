import LogicLineages.PersistentMarking.NumberedWindowTupleAuxLambdaCase
import LogicLineages.PersistentMarking.NumberedWindowTupleAuxHeadCases

namespace LogicLineages.PersistentMarking.NumberedWindowTupleAuxFoldProof
open Spine NumberedWindowTupleAuxGoals

theorem run (S : Signature) (K : List Ty) (C : BoundContext) (n B : Nat)
    (args : Spine.Args) : ForArgs S K C n B args := by
  cases args with
  | nil => exact nilCase S K C n B
  | cons a rest =>
    intro q
    cases q with
    | free α x =>
      intro values types σ τ r Q As Vs hk hBudget hW hV hCall hv hu hr
      simp [Spine.applyAux] at hr
    | bound α i =>
      intro values types σ τ r Q As Vs hk hBudget hW hV hCall hv hu hr
      simp [Spine.applyAux] at hr
    | lam α body =>
      exact NumberedWindowTupleAuxLambdaCase.lambdaCase S K C n B a rest α body (run S K C n B rest)
    | head f bs => exact NumberedWindowTupleAuxHeadCases.ordinaryCase S K C n B a rest f bs
    | marked f δ bs es => exact NumberedWindowTupleAuxHeadCases.markedCase S K C n B a rest f δ bs es
termination_by structural args

end LogicLineages.PersistentMarking.NumberedWindowTupleAuxFoldProof
