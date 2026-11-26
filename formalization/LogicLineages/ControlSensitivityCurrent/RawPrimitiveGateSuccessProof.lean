module
public import LogicLineages.ControlSensitivityCurrent.RawPrimitiveGateForestProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PrimitiveGate

open LogicLineages.OrdinalComparison.Source GroundEquivalence PrimitiveLowering

theorem success_reconstruction : RawPrimitiveGateTargets.SuccessReconstruction := by
  intro context raw out h
  have hg : gateGuard context raw = true := by
    unfold compile at h
    split at h
    next hg => exact hg
    next hg => simp at h
  let Γ := context.map SyntaxCode.decodeType
  have hc : Γ.map SyntaxCode.typeCode = context := encode_types context
  obtain ⟨g,he⟩ := (gate_exactness Γ raw).mp (by rw [hc]; exact hg)
  have htyped := forest_exactness Γ g
  rw [hc, he, h] at htyped
  exact ⟨Γ, g, hc, he, Option.some.inj htyped, fun e _ =>
    ⟨input_roundtrip _, input_roundtrip _⟩⟩

theorem rejection_and_counts : RawPrimitiveGateTargets.RejectionAndCounts := by
  constructor
  · intro context raw
    cases hg : gateGuard context raw <;> simp [compile, hg]
  · intro context raw out h
    obtain ⟨Γ, g, hc, he, ho, _⟩ := success_reconstruction context raw out h
    subst out
    refine ⟨?_, ?_⟩
    · rw [RawPrimitiveGateTargets.encodeForest, List.length_map]
      cases g <;> rfl
    · intro e hmem
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hmem
      have hb : (Block Γ).map SyntaxCode.typeCode = blockContext context := by
        rw [block_context_code, hc]
      exact ⟨typedAccepted _, typedAccepted _, hb, hb⟩

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PrimitiveGate
