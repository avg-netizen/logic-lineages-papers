module
public import LogicLineages.ControlSensitivityCurrent.RawPlanRenamingTargets
public import LogicLineages.ControlSensitivityCurrent.RawPlanCompilerEmbeddingProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanRenaming

open LogicLineages.OrdinalComparison.Source ExistentialPlan
open PlanCompiler (Instruction encodePlan renaming_comp_codes rename_gate_code)
open Operations (renamingCode rename_input)

theorem renaming_lift_code {Γ Θ : List Ty} (r : Renaming Γ Θ) :
    liftTable (renamingCode r) = renamingCode (Renaming.lift (τ := .ground) r) := by
  have hs := renaming_comp_codes r (Renaming.weaken Θ .ground) Nat.succ (fun _ => rfl)
  change 0 :: (renamingCode r).map Nat.succ =
    0 :: renamingCode (fun x => Variable.there (r x))
  rw [← hs]
  rfl

private theorem rename_scan_exact {Γ : List Ty} (q : Plan Γ) :
    ∀ (Θ : List Ty) (r : Renaming Γ Θ) (rev : List Instruction),
      ((encodePlan q).foldl renameStep (Θ.map SyntaxCode.typeCode,renamingCode r,rev)).2.2.reverse =
        rev.reverse ++ encodePlan (BinaryPlan.renamePlan r q) := by
  induction q with
  | done =>
      intro Θ r rev
      simp [encodePlan, BinaryPlan.renamePlan]
  | @equation Γ a b tail ih =>
      intro Θ r rev
      simp only [encodePlan, List.foldl_cons, renameStep, ← rename_input]
      rw [ih]
      simp [BinaryPlan.renamePlan, encodePlan, List.reverse_cons, List.append_assoc]
  | @gate Γ g tail ih =>
      intro Θ r rev
      simp only [encodePlan, List.foldl_cons, renameStep, rename_gate_code]
      rw [ih]
      simp [BinaryPlan.renamePlan, encodePlan, List.reverse_cons, List.append_assoc]
  | @existsGround Γ tail ih =>
      intro Θ r rev
      simp only [encodePlan, List.foldl_cons, renameStep, renaming_lift_code]
      rw [show (0 :: Θ.map SyntaxCode.typeCode) =
        (Ty.ground :: Θ).map SyntaxCode.typeCode from rfl, ih]
      simp [BinaryPlan.renamePlan, encodePlan, List.reverse_cons, List.append_assoc]

theorem typed_exactness : RawPlanRenamingTargets.TypedExactness := by
  intro Γ Θ r q
  simpa only [renamePlanRaw, List.reverse_nil, List.nil_append] using rename_scan_exact q Θ r []

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanRenaming
