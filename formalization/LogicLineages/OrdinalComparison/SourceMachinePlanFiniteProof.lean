module
public import LogicLineages.OrdinalComparison.SourceMachinePlanFinitePreservationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachinePlanFinite.Proof
open ExistentialPlan BinaryPlan PrimitiveLowering ParametricPlanFinite ParametricScalingPlan
open SourceMachineConjunctionPlan

theorem tail_finite (G : Nat → Nat) (hm : StrictMono G) (hi : ∀ n : Nat,n ≤ G n) (e : Nat) :
    UniformFinite G (tail e) := by
  apply scale_finite G e
  refine ⟨?_,trivial⟩
  intro ρ
  refine ⟨ParametricPrimitiveFinite.value G (inputs ρ) (.successor (port 10))+1,
    ParametricPrimitiveFinite.value G (inputs ρ) (.port (port 11))+1,?_,?_⟩
  · rw [(PrimitiveLowering.Proof.primitiveRealization _ (.successor (port 10))).1]
    exact (ParametricPrimitiveFinite.Proof.exactExpressionCalibration G hm hi _ (inputs ρ) _).1
  · rw [(PrimitiveLowering.Proof.primitiveRealization _ (.port (port 11))).1]
    exact (ParametricPrimitiveFinite.Proof.exactExpressionCalibration G hm hi _ (inputs ρ) _).1

theorem actualPlanUniformity : Targets.ActualPlanUniformity := by
  intro G hm hi b e
  apply constructorPreservation.2.1 G
  apply constructorPreservation.2.1 G
  apply constructorPreservation.2.1 G
  exact tail_finite G hm hi e

theorem actualGammaForest : Targets.ActualGammaForest := by
  intro b e
  have h := ParametricCoefficientOne.Proof.actualGammaCoefficientOne b
  exact ParametricPlanFinite.Proof.actualGammaCompiler b _ (plan b e)
    (actualPlanUniformity _ h.1 h.2.1 b e)
end LogicLineages.OrdinalComparison.Source.SourceMachinePlanFinite.Proof
