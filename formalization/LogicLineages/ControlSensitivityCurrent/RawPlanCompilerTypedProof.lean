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
      have ha := CheckedRenaming.typed_exactness Γ (compile q).context .ground (compile q).embedding a
      have hb := CheckedRenaming.typed_exactness Γ (compile q).context .ground (compile q).embedding b
      simp only [compileStep, encodeResult, equation_guard_typed, Bool.not_true, Bool.false_eq_true,
        ite_false, ha, hb]
      rfl
  | @gate Γ g q ih =>
      have hg := (PrimitiveGate.gate_exactness Γ _).mpr ⟨g,rfl⟩
      simp only [encodePlan, run_state_cons, pushContext, ih, Option.bind_some]
      have hw := PrimitiveGate.forest_exactness (compile q).context (gateRename (compile q).embedding g)
      simp only [compileStep, encodeResult, hg, Bool.not_true, Bool.false_eq_true, ite_false,
        rename_gate_code, hw, shift_forest_code, compile,
        PrimitiveGate.block_context_code, shifted_embedding]
      simp only [encodeForest, List.map_append] <;> rfl
  | @existsGround Γ q ih =>
      simp only [encodePlan, run_state_cons, pushContext]
      change (runState ((Ty.ground :: Γ).map SyntaxCode.typeCode) (encodePlan q)).bind _ = _
      rw [ih]
      rfl

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanCompiler
