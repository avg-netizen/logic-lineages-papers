module
public import LogicLineages.PermittedControl.OriginalNormalizedMatrixPositiveSnapshotsTargets
import LogicLineages.PermittedControl.OriginalNormalizedMatrixPositiveSnapshotsShapeProof
import LogicLineages.PermittedControl.OriginalNormalizedMatrixPositiveSnapshotsGateProof
import LogicLineages.PermittedControl.OriginalNormalizedCircuitMatrixProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalNormalizedMatrixPositiveSnapshots
open OriginalPrintedCircuitNormalization (NormalizedGate)
open OriginalNormalizedCircuitMatrix (rows passing rowsList passingList exactNormalizedCircuitRows)
open HeterogeneousSignedMatrixSlice (Snapshot)

theorem exactPositiveCircuitSnapshots : ExactPositiveCircuitSnapshots := by
  intro f θ gs snap
  have shape (s : Snapshot) (h : HeterogeneousSignedMatrixSlice.actualRows f θ (rowsList gs) s)
      (yes : AllTrue s) : s = passingList θ gs := by
    induction gs generalizing s with
    | nil =>
        cases s with
        | nil => rfl
        | cons v s => exact False.elim h
    | cons g gs ih =>
        obtain ⟨xs,ys,eq,hx,hy⟩ := splitActual f θ (rows g) (rowsList gs) s h
        rw [eq] at yes
        have truth := (allAppend xs ys).mp yes
        have gx := gateShape f θ g xs hx truth.1
        have gy := ih ys hy truth.2
        rw [eq,gx,gy] <;> rfl
  have passes : AllTrue (passingList θ gs) := by
    induction gs with
    | nil => simp [passingList,AllTrue]
    | cons g gs ih => exact (allAppend (passing θ g) (passingList θ gs)).mpr ⟨gateTrue θ g,ih⟩
  have original := (exactNormalizedCircuitRows f θ gs).2
  constructor
  · rintro ⟨actual,yes⟩
    have eq := shape snap actual yes
    exact ⟨original.mp (eq ▸ actual),eq⟩
  · rintro ⟨graph,rfl⟩
    exact ⟨original.mpr graph,passes⟩

end LogicLineages.PermittedControl.OriginalNormalizedMatrixPositiveSnapshots
