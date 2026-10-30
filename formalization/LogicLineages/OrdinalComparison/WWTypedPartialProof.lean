module
public import LogicLineages.OrdinalComparison.WWTypedPartialTargets
public import Lean.Elab.Tactic.Omega

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem actualTypedHeadFreeCalibration : Targets.ActualTypedHeadFreeCalibration := by
  intro Γ σ t
  induction t with
  | var c =>
    rcases c with ⟨τ, v, i⟩
    cases v <;> simp [ordinalHeadFree, ordinalHeadOccurs, ordinalHeadComponentOccurs,
      ordinalExpressionRename, ordinalHeadClosure, substitute, ordinalHeadClosureComponent,
      ordinalComponentRename, Renaming.weaken]
  | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | one => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | omega => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | add f g hf hg =>
    simpa [ordinalHeadFree, ordinalHeadOccurs, ordinalExpressionRename, ordinalHeadClosure,
      substitute] using and_congr hf hg
  | emul f g hf hg =>
    simpa [ordinalHeadFree, ordinalHeadOccurs, ordinalExpressionRename, ordinalHeadClosure,
      substitute] using and_congr hf hg
  | collapse f g hf hg =>
    simpa [ordinalHeadFree, ordinalHeadOccurs, ordinalExpressionRename, ordinalHeadClosure,
      substitute] using and_congr hf hg

theorem actualTypedPartialSize : Targets.ActualTypedPartialSize := by
  intro Γ σ t
  constructor
  · induction t <;> rw [ordinalPartialSize] <;> split <;> omega
  · intro h
    rw [ordinalPartialSize.eq_def, h]
    rfl

theorem actualTypedFreePartial : Targets.ActualTypedFreePartial := by
  intro Γ σ i t h
  rw [ordinalTypedPartial.eq_def, h]
  rfl

theorem actualTypedVariablePartial : Targets.ActualTypedVariablePartial := by
  intro Γ σ i k
  rw [ordinalTypedPartial]
  rfl

theorem actualTypedSumPartial : Targets.ActualTypedSumPartial := by
  intro Γ σ i f g h
  rw [ordinalTypedPartial, h]
  rfl

theorem actualTypedExponentialPartial : Targets.ActualTypedExponentialPartial := by
  intro Γ σ i f g h
  rw [ordinalTypedPartial, h]
  rfl

theorem actualTypedCollapsePartial : Targets.ActualTypedCollapsePartial := by
  intro Γ σ i f g h
  rw [ordinalTypedPartial, h]
  rfl

end LogicLineages.OrdinalComparison.Source
