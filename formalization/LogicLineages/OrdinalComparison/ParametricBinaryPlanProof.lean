module
public import LogicLineages.OrdinalComparison.ParametricBinaryPlanSemanticProof
public import LogicLineages.OrdinalComparison.SourceExistentialPlanSizeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricBinaryPlan.Proof
open PrimitiveLowering ExistentialPlan BinaryPlan ParametricExistentialPlan

theorem actualGammaLiteralCompilation : Targets.ActualGammaLiteralCompilation := by
  intro b k Γ q hs ρ
  have hp : Supported (constantPlan k q) := (binary_supported _ _ q).mpr hs
  rw [← ParametricExistentialPlan.Proof.actualGammaCompilation b Γ (constantPlan k q) hp ρ]
  exact literal_correct _ ρ k q

theorem exactCompiledBounds : Targets.ExactCompiledBounds := by
  intro Γ k q
  have hp := ExistentialPlan.Proof.size Γ (constantPlan k q)
  have hb := BinaryPlan.Proof.literalSize Γ k q
  exact ⟨hp.1.trans hb.1,by omega,by omega⟩
end LogicLineages.OrdinalComparison.Source.ParametricBinaryPlan.Proof
