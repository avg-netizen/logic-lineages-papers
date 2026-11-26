module
public import LogicLineages.ControlSensitivityCurrent.RawCheckedRenamingTableProof
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGOperationsStructuralProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.CheckedRenaming

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source GroundEquivalence

theorem typed_exactness : RawCheckedRenamingTargets.TypedExactness := by
  intro Γ Θ τ r d
  have hg : guard (Θ.map SyntaxCode.typeCode) (Operations.renamingCode r)
      (encode ⟨Γ,τ,d⟩) = true := by
    rw [guard, Bool.and_eq_true]
    exact ⟨typedAccepted _, (table_exactness Γ Θ _).mpr ⟨r, rfl⟩⟩
  simp only [rename, hg, ite_true, Operations.rename_input]

theorem success_reconstruction : RawCheckedRenamingTargets.SuccessReconstruction := by
  intro target table c out h
  have hg : guard target table c = true := by
    unfold rename at h
    split at h
    next hg => exact hg
    next hg => simp at h
  obtain ⟨hv, ht⟩ := Bool.and_eq_true.mp hg
  obtain ⟨⟨Γ,τ,d⟩, hd⟩ := (valid_iff c).mp hv
  subst c
  let Θ := target.map SyntaxCode.decodeType
  have hΘ : Θ.map SyntaxCode.typeCode = target := encode_types target
  have htable : tableGuard (Γ.map SyntaxCode.typeCode) (Θ.map SyntaxCode.typeCode) table = true := by
    rw [hΘ]
    exact ht
  obtain ⟨r, hr⟩ := (table_exactness Γ Θ table).mp htable
  have htyped := typed_exactness Γ Θ τ r d
  rw [hΘ, hr, h] at htyped
  exact ⟨Γ, Θ, τ, r, d, rfl, hΘ, hr, Option.some.inj htyped, by
    rw [Option.some.inj htyped, input_roundtrip]⟩

theorem rejection_and_counts : RawCheckedRenamingTargets.RejectionAndCounts := by
  constructor
  · intro target table c
    cases hg : guard target table c <;> simp [rename, hg]
  · intro target table c out h
    obtain ⟨Γ, Θ, τ, r, d, hc, hΘ, hr, ho, _⟩ := success_reconstruction target table c out h
    refine ⟨by rw [ho]; exact typedAccepted _, ?_⟩
    have hout : Operations.renameCode target table c = out := by
      rw [← hΘ, ← hr, ← hc, ← Operations.rename_input, ho]
    rw [← hout]
    simp [Operations.renameCode, Operations.renameTable]

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.CheckedRenaming
