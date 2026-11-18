module
public import LogicLineages.ControlSensitivityCurrent.RawPlanCompilerEmbeddingProof
public import LogicLineages.ControlSensitivityCurrent.RawCheckedRenamingProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanCompiler

open LogicLineages.OrdinalComparison.Source ExistentialPlan GroundEquivalence
open RawPrimitiveGateTargets (encodeForest)

theorem run_state_cons (context : List Nat) (i : Instruction) (code : List Instruction) :
    runState context (i :: code) = (runState (pushContext context i) code).bind (compileStep i) :=
  rfl

private theorem equation_guard_typed {Γ : List Ty} (a b : Input Γ .ground) :
    equationGuard (Γ.map SyntaxCode.typeCode) (encode ⟨Γ,.ground,a⟩) (encode ⟨Γ,.ground,b⟩) =
      true := by
  simp [equationGuard, encode, SyntaxCode.typeCode]

theorem typed_exactness : RawPlanCompilerTargets.TypedExactness := by
  intro Γ q
  induction q with
  | @done Γ =>
      simp [encodePlan, runState, endContext, compile, encodeResult, identity_table, encodeForest]
  | @equation Γ a b q ih =>
      simp only [encodePlan, run_state_cons, pushContext, ih, Option.bind_some]
      simp [compileStep, encodeResult, equation_guard_typed, CheckedRenaming.typed_exactness,
        compile, encodeForest]
  | @gate Γ g q ih =>
      have hg := (PrimitiveGate.gate_exactness Γ _).mpr ⟨g,rfl⟩
      simp only [encodePlan, run_state_cons, pushContext, ih, Option.bind_some]
      simp [compileStep, encodeResult, hg, rename_gate_code, PrimitiveGate.forest_exactness,
        compile, PrimitiveGate.block_context_code, shifted_embedding, shift_forest_code,
        encodeForest]
  | @existsGround Γ q ih =>
      simp only [encodePlan, run_state_cons, pushContext]
      change (runState ((Ty.ground :: Γ).map SyntaxCode.typeCode) (encodePlan q)).bind _ = _
      simp [ih, compileStep, encodeResult, compile, renaming_tail, SyntaxCode.typeCode]

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanCompiler
