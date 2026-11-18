module
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGRoundtripProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open GroundEquivalence

theorem variable_index_sound (Γ : List Ty) (τ : Ty) (i : Nat) (x : Variable Γ τ)
    (h : getVariable Γ τ i = some x) : variableIndex x = i := by
  induction Γ generalizing i with
  | nil => simp [getVariable] at h
  | cons σ Γ ih =>
      cases i with
      | zero =>
          simp only [getVariable] at h
          split at h
          next he => cases he; cases Option.some.inj h; rfl
          next he => simp at h
      | succ i =>
          simp only [getVariable,Option.map_eq_some_iff] at h
          obtain ⟨y,hy,hx⟩ := h
          subst x
          simp [variableIndex,ih i y hy]

theorem reference_index_sound (ss : List Spec) (s : Spec) (i : Nat) (r : Ref ss s)
    (h : getReference ss s i = some r) : referenceIndex r = i := by
  induction ss generalizing i with
  | nil => simp [getReference] at h
  | cons t ss ih =>
      cases i with
      | zero =>
          simp only [getReference] at h
          split at h
          next he => cases he; cases Option.some.inj h; rfl
          next he => simp at h
      | succ i =>
          simp only [getReference,Option.map_eq_some_iff] at h
          obtain ⟨r',hr,he⟩ := h
          subst r
          simp [referenceIndex,ih i r' hr]
end LogicLineages.ControlSensitivityCurrent.RawSourceDAG
