module
public import LogicLineages.PermittedControl.OriginalPrintedRawSelectedStageQueryTargets
import LogicLineages.PermittedControl.OriginalPrintedRawStageQueryProof
import LogicLineages.PermittedControl.ControlProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawSelectedStageQuery
open OriginalPrintedRawStageQuery (exactOriginalRawStageQuery exactOriginalRawStageFailure
  originalRawStageQueryEffectivity)

theorem selectedControlEffectivity (f : Nat → Nat) (B : Nat)
    (h : SelectedWithThreshold f B) : Primrec f := by
  rcases h with ⟨rfl,rfl⟩ | ⟨b,rfl,rfl⟩
  · exact factorial_control_laws.2.1
  · exact (near_control_laws b).2.1

private theorem forSelected (f : Nat → Nat) (B : Nat)
    (h : SelectedWithThreshold f B) : ForControl f B :=
  ⟨exactOriginalRawStageQuery f B,
    fun high hh => originalRawStageQueryEffectivity f B high
      (selectedControlEffectivity f B h).to_comp hh⟩

theorem exactOriginalRawSelectedStageQuery : ExactOriginalRawSelectedStageQuery := by
  constructor
  · exact forSelected factorialControl 0 (Or.inl ⟨rfl,rfl⟩)
  · intro b
    exact forSelected (nearControl b) (b + 1) (Or.inr ⟨b,rfl,rfl⟩)

theorem fullOriginalRawSelectedStageQuery : FullOriginalRawSelectedStageQuery :=
  ⟨exactOriginalRawSelectedStageQuery,exactOriginalRawStageFailure⟩

end LogicLineages.PermittedControl.OriginalPrintedRawSelectedStageQuery
