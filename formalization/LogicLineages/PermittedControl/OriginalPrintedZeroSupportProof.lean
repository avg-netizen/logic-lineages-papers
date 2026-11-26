module
public import LogicLineages.PermittedControl.OriginalPrintedZeroSupportTargets
import LogicLineages.PermittedControl.OriginalPrintedZeroSupportSnapshotProof
import LogicLineages.PermittedControl.OriginalNormalizedMatrixPositiveSnapshotsProof
import LogicLineages.PermittedControl.OriginalPlainTerminalMatrixProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedZeroSupport
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedPlainMatrixInfiniteLow (matrix circuit)
open OriginalNormalizedCircuitMatrix (rowsList passingList)
open OriginalMatrixDenseRanks (support)
open OriginalPlainTerminalMatrix (rows accepts readBits exactPlainTerminalSuffix)
open OriginalNormalizedMatrixPositiveSnapshots (AllTrue exactPositiveCircuitSnapshots)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)

private theorem finished (p : NormalForm.Formula) (graph tail : Snapshot) (b : Bool) :
    finish p graph tail = some b ↔ AllTrue graph ∧ accepts p b tail := by
  have yes : graph.all Prod.snd = true ↔ AllTrue graph := List.all_eq_true
  by_cases allTrue : graph.all Prod.snd = true
  · have graphHolds := yes.mp allTrue
    cases read : readBits p (tail.map Prod.snd) with
    | none => simp [finish,allTrue,accepts,read]
    | some output =>
      rcases output with ⟨actual,leftover⟩
      cases leftover <;> simp [finish,allTrue,accepts,read,graphHolds]
  · have dead : ¬ AllTrue graph := fun h => allTrue (yes.mpr h)
    simp [finish,allTrue,dead]

private theorem allEmpty (rs : List Row) (h : support rs = []) :
    ∀ r ∈ rs, r.2.2 = [] := by
  intro r used
  cases t : r.2.2 with
  | nil => rfl
  | cons a as =>
    have present : a ∈ r.2.2 := by rw [t]; exact List.mem_cons_self
    have impossible : a.2.rank ∈ support rs :=
      List.mem_flatMap.mpr ⟨r,used,List.mem_map.mpr ⟨a,present,rfl⟩⟩
    rw [h] at impossible
    cases impossible

theorem exactOriginalZeroSupport : ExactOriginalZeroSupport := by
  intro f θ known gates p plain empty positive
  let gs := circuit known gates p
  let pre := rowsList gs
  let tail := rows p
  have prefixEmpty (r : Row) (used : r ∈ pre) : r.2.2 = [] :=
    allEmpty (matrix known gates p) empty r (List.mem_append_left _ used)
  have suffixEmpty (r : Row) (used : r ∈ tail) : r.2.2 = [] :=
    allEmpty (matrix known gates p) empty r (List.mem_append_right _ used)
  have exec (snap : Snapshot) : closedSnapshot pre = some snap ↔ actualRows f θ pre snap :=
    (exactClosedActualSnapshot f θ pre snap).trans ⟨And.right,fun h => ⟨prefixEmpty,h⟩⟩
  have execSuffix (snap : Snapshot) : closedSnapshot tail = some snap ↔ actualRows f θ tail snap :=
    (exactClosedActualSnapshot f θ tail snap).trans ⟨And.right,fun h => ⟨suffixEmpty,h⟩⟩
  have terminal := exactPlainTerminalSuffix f θ p plain positive
  constructor
  · intro read
    change (closedSnapshot pre).bind (fun g => (closedSnapshot tail).bind (finish p g)) = some positive at read
    cases graphResult : closedSnapshot pre with
    | none => rw [graphResult] at read; cases read
    | some graph =>
      cases tailResult : closedSnapshot tail with
      | none => rw [graphResult,tailResult] at read; cases read
      | some snap =>
        rw [graphResult,tailResult] at read
        obtain ⟨allTrue,tested⟩ := (finished p graph snap positive).mp read
        exact ⟨((exactPositiveCircuitSnapshots f θ gs graph).mp ⟨(exec graph).mp graphResult,allTrue⟩).1,
          terminal.mpr ⟨snap,(execSuffix snap).mp tailResult,tested⟩⟩
  · rintro ⟨normalized,test⟩
    let graph := passingList θ gs
    obtain ⟨correct,allTrue⟩ := (exactPositiveCircuitSnapshots f θ gs graph).mpr ⟨normalized,rfl⟩
    obtain ⟨snap,actual,tested⟩ := terminal.mp test
    change (closedSnapshot pre).bind (fun g => (closedSnapshot tail).bind (finish p g)) = some positive
    rw [(exec graph).mpr correct,(execSuffix snap).mpr actual]
    exact (finished p graph snap positive).mpr ⟨allTrue,tested⟩

end LogicLineages.PermittedControl.OriginalPrintedZeroSupport
