module
public import LogicLineages.OrdinalComparison.SourceTypedPortsTargets
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Finset.Card
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceTypedPortsProof
open SourceTypedPorts SourceTypedPortsTargets SourceFreeOccurrences

theorem typedVariableEnumeration : TypedVariableEnumeration := by
  intro Γ
  induction Γ with
  | nil => intro σ v; cases v
  | cons τ Γ ih =>
    intro σ v
    cases v with
    | here => simp [enumerateVariables]
    | there v =>
      exact List.mem_append_right _ (List.mem_map.mpr ⟨v, ih _ v, rfl⟩)

private theorem index_bound {Γ : List Ty} {σ : Ty} (v : Variable Γ σ) :
    variableIndex v < Γ.length := by
  induction v with
  | here => exact Nat.zero_lt_succ _
  | there v ih => exact Nat.succ_lt_succ ih

private theorem packed_index_injective (Γ : List Ty) (v w : PackedVariable Γ)
    (h : variableIndex v.2 = variableIndex w.2) : v = w := by
  induction Γ with
  | nil => cases v.2
  | cons τ Γ ih =>
    rcases v with ⟨σ, v⟩
    rcases w with ⟨υ, w⟩
    cases v with
    | here =>
      cases w with
      | here => rfl
      | there w => simp [variableIndex] at h
    | there v =>
      cases w with
      | here => simp [variableIndex] at h
      | there w =>
        have he := ih ⟨_, v⟩ ⟨_, w⟩ (Nat.add_right_cancel h)
        cases he
        rfl

theorem typedVariableIndex : TypedVariableIndex :=
  ⟨fun _ _ v => index_bound v, packed_index_injective⟩

private theorem all_maps {Θ Λ : List Ty} (a : PortMap Θ Λ) : a ∈ allMaps Θ Λ := by
  induction a with
  | nil => simp [allMaps]
  | cons v rest ih =>
    exact List.mem_flatMap.mpr ⟨v, typedVariableEnumeration _ _ v, List.mem_map.mpr ⟨rest, ih, rfl⟩⟩

theorem typedAssignmentEnumeration : TypedAssignmentEnumeration := by
  intro Θ Λ a
  simp only [injectiveMaps, List.mem_filter, decide_eq_true_eq]
  exact and_iff_right (all_maps a)

private theorem index_embed {Θ : List Ty} {σ : Ty} (Γ : List Ty) (v : Variable Θ σ) :
    variableIndex (embedLeft Γ v) = variableIndex v := by
  induction v with
  | here => rfl
  | there v ih => exact congrArg (fun n => n + 1) ih

theorem assignmentRenamingCalibration : AssignmentRenamingCalibration := by
  intro Γ Θ Λ a
  induction a with
  | nil =>
    constructor
    · intros; rfl
    · intro σ v; cases v
  | cons v rest ih =>
    constructor
    · intro σ w
      exact ih.1 σ w
    · intro σ w
      cases w with
      | here => exact index_embed Γ v
      | there w => exact ih.2 σ w

private theorem shift_indices (σ : Ty) {Θ Λ : List Ty} (a : PortMap Θ Λ) :
    indices (shiftMap σ a) = (indices a).map Nat.succ := by
  induction a with
  | nil => rfl
  | cons v rest ih => simp [shiftMap, indices, variableIndex, ih]

private theorem rename_shift (Γ : List Ty) (σ : Ty) {Θ Λ : List Ty}
    (a : PortMap Θ Λ) : ∀ {τ : Ty} (v : Variable (Λ ++ Γ) τ),
    renameWith Γ (shiftMap σ a) v = Variable.there (renameWith Γ a v) := by
  induction a with
  | nil => intros; rfl
  | cons v rest ih =>
    intro τ w
    cases w with
    | here => rfl
    | there w => exact ih w

theorem assignmentLift : AssignmentLift := by
  intro Γ Θ Λ σ a
  constructor
  · intro hn
    change (0 :: indices (shiftMap σ a)).Nodup
    rw [shift_indices, List.nodup_cons]
    exact ⟨by simp, List.Nodup.map Nat.succ_injective hn⟩
  · funext τ v
    cases v with
    | here => rfl
    | there v => exact rename_shift Γ σ a v

theorem freshPortAvailability : FreshPortAvailability := by
  intro B P hn hlen
  classical
  by_contra h
  push_neg at h
  have hu : (Finset.univ : Finset (Fin B)) ⊆ (P.map Prod.fst).toFinset := by
    intro i _
    exact List.mem_toFinset.mpr (h i)
  have hc := Finset.card_le_card hu
  rw [Finset.card_univ, Fintype.card_fin, List.toFinset_card_of_nodup hn, List.length_map] at hc
  omega

end LogicLineages.OrdinalComparison.Source.SourceTypedPortsProof
