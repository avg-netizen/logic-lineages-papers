module
public import LogicLineages.OrdinalComparison.ParametricBinaryPlanTargets
public import LogicLineages.OrdinalComparison.ParametricExistentialPlanProof
public import LogicLineages.OrdinalComparison.SourceBinaryPlanProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricBinaryPlan.Proof
open GroundEquivalence PrimitiveLowering ExistentialPlan SourceAdditionCompletion BinaryPlan ParametricExistentialPlan
theorem rename_correct (G : Nat → Nat) : ∀ (Γ Δ : List Ty) (r : Renaming Γ Δ)
    (ρ : Variable Γ .ground → Nat) (ν : Variable Δ .ground → Nat),
    (∀ x,ν (r x)=ρ x) → ∀ q : Plan Γ, EvalWith G ν (renamePlan r q) ↔ EvalWith G ρ q := by
  intro Γ Δ r ρ ν h q
  induction q generalizing Δ with
  | done => rfl
  | equation a b q ih =>
      simp only [renamePlan,EvalWith]
      apply and_congr
      · exact ParametricExistentialPlan.Proof.equation_dag_rename G r ρ ν h a b
      · apply ih
        exact h
  | gate g q ih =>
      simp only [renamePlan,EvalWith]
      apply and_congr
      · exact ExistentialPlan.Proof.gate_rename r ρ ν h g
      · apply ih
        exact h
  | existsGround q ih =>
      simp only [renamePlan,EvalWith]
      apply exists_congr
      intro x
      apply ih
      intro y
      cases y with
      | here => rfl
      | there y => exact h y


theorem rename_supported {Γ Δ : List Ty} (r : Renaming Γ Δ) (q : Plan Γ) :
    Supported (renamePlan r q) ↔ Supported q := by
  induction q generalizing Δ with
  | done => rfl
  | equation a b q ih => exact ih r
  | gate g q ih =>
      simp only [renamePlan,Supported,ih]
      cases g <;> rfl
  | existsGround q ih => exact ih (Renaming.lift r)

theorem exactRenaming : Targets.ExactRenaming :=
  ⟨rename_correct,fun _ _ r q => rename_supported r q⟩
end LogicLineages.OrdinalComparison.Source.ParametricBinaryPlan.Proof
