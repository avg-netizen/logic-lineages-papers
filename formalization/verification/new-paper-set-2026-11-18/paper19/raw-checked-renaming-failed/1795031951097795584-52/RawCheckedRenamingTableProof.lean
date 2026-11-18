module
public import LogicLineages.ControlSensitivityCurrent.RawCheckedRenamingTargets
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGRawValidatorLookupProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.CheckedRenaming

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open Operations (renamingCode)

private theorem scan_none (source target : List Nat) :
    source.foldl (scanEntry target) none = none := by
  induction source with
  | nil => rfl
  | cons t source ih =>
      simpa only [List.foldl_cons, scanEntry] using ih

private theorem table_guard_cons (t i : Nat) (source target table : List Nat) :
    tableGuard (t :: source) target (i :: table) =
      (RawValidator.«variable» target t i && tableGuard source target table) := by
  cases h : RawValidator.«variable» target t i <;>
    simp [tableGuard, List.foldl_cons, scanEntry, h, scan_none]

private def consRenaming {Γ Θ : List Ty} {τ : Ty} (y : Variable Θ τ)
    (r : Renaming Γ Θ) : Renaming (τ :: Γ) Θ
  | _, .here => y
  | _, .there x => r x

theorem table_exactness : RawCheckedRenamingTargets.TableExactness := by
  intro Γ Θ table
  induction Γ generalizing table with
  | nil =>
      constructor
      · intro h
        have ht : table = [] := by simpa [tableGuard] using h
        subst table
        exact ⟨fun x => nomatch x, rfl⟩
      · rintro ⟨r, rfl⟩
        rfl
  | cons τ Γ ih =>
      constructor
      · intro h
        cases table with
        | nil => simp [tableGuard, scanEntry, scan_none] at h
        | cons i table =>
            rw [List.map_cons, table_guard_cons, Bool.and_eq_true] at h
            have hi : (getVariable Θ τ i).isSome := by
              simpa only [RawValidator.variable_status] using h.1
            obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hi
            obtain ⟨r, hr⟩ := (ih table).mp h.2
            exact ⟨consRenaming y r, by
              change variableIndex y :: renamingCode r = i :: table
              rw [variable_index_sound Θ τ i y hy, hr]⟩
      · rintro ⟨r, rfl⟩
        change tableGuard (SyntaxCode.typeCode τ :: Γ.map SyntaxCode.typeCode)
          (Θ.map SyntaxCode.typeCode)
          (variableIndex (r Variable.here) :: renamingCode (fun x => r (Variable.there x))) = true
        rw [table_guard_cons, Bool.and_eq_true, RawValidator.variable_status, variable_roundtrip]
        exact ⟨rfl, (ih _).mpr ⟨fun x => r (Variable.there x), rfl⟩⟩

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.CheckedRenaming
