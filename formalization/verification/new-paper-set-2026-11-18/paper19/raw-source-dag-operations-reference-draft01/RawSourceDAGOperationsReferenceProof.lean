module
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGOperationsTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.Operations
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source GroundEquivalence

theorem front_index (tail : List Spec) {ss s} (r : Ref ss s) :
    referenceIndex (ScopedDAG.Ref.front tail r) = referenceIndex r := by
  induction r <;> simp_all [ScopedDAG.Ref.front,referenceIndex]
theorem back_index (front : List Spec) {ss s} (r : Ref ss s) :
    referenceIndex (ScopedDAG.Ref.back front r) = front.length + referenceIndex r := by
  induction front <;> simp_all [ScopedDAG.Ref.back,referenceIndex,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
theorem map_index {ss s} (r : Ref ss s) : referenceIndex (r.map insertSpec) = referenceIndex r := by
  induction r <;> simp_all [Ref.map,referenceIndex]

theorem renaming_length {Γ Θ} (r : Renaming Γ Θ) : (renamingCode r).length = Γ.length := by
  induction Γ with
  | nil => rfl
  | cons σ Γ ih => simp [renamingCode,ih]

theorem renaming_lookup {Γ Θ τ} (r : Renaming Γ Θ) (x : Variable Γ τ) :
    (renamingCode r).getD (variableIndex x) 0 = variableIndex (r x) := by
  induction x with
  | here => rfl
  | there x ih => simpa [renamingCode,variableIndex] using ih (fun y => r (.there y))

theorem prefix_index {Γ Θ} (ps : List Ty) (r : Renaming Γ Θ) {τ} (x : Variable (ps++Γ) τ) :
    variableIndex (ScopedDAG.prefixRename r ps x) = renameIndex ps.length (renamingCode r) (variableIndex x) := by
  induction ps with
  | nil => simpa [ScopedDAG.prefixRename,renameIndex] using (renaming_lookup r x).symm
  | cons σ ps ih =>
      cases x with
      | here => simp [ScopedDAG.prefixRename,Renaming.lift,variableIndex,renameIndex]
      | there x =>
          simpa [ScopedDAG.prefixRename,Renaming.lift,variableIndex,renameIndex,
            Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using congrArg Nat.succ (ih x)

theorem insertion_index (Γ ps : List Ty) {τ} (x : Variable (ps++Γ) τ) :
    variableIndex (insertGround Γ ps x) = insertIndex ps.length (variableIndex x) := by
  induction ps with
  | nil => simp [insertGround,Renaming.weaken,variableIndex,insertIndex]
  | cons σ ps ih =>
      cases x with
      | here => simp [insertGround,Renaming.lift,variableIndex,insertIndex]
      | there x =>
          simpa [insertGround,Renaming.lift,variableIndex,insertIndex,
            Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using congrArg Nat.succ (ih x)

theorem references : RawSourceDAGOperationsTargets.References :=
  ⟨fun tail _ _ r => front_index tail r,fun front _ _ r => back_index front r,
    fun _ _ r => map_index r,fun _ _ ps r _ x => prefix_index ps r x,
    fun Γ ps _ x => insertion_index Γ ps x⟩
end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.Operations
