module
public import LogicLineages.OrdinalComparison.ParametricScalingPlanTargets
public import LogicLineages.OrdinalComparison.SourceBinaryPlanProof
public import LogicLineages.OrdinalComparison.SourceExistentialPlanSizeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricScalingPlan.Proof
open PrimitiveLowering ExistentialPlan BinaryPlan

theorem plan_size {Γ} (e : Nat) (a out : Port Γ) (q : Plan Γ) :
    (scalePlan e a out q).vertices=80*(e+1)+q.vertices ∧
    (scalePlan e a out q).equations=10*(e+1)+q.equations ∧
    (scalePlan e a out q).witnesses=10*e+9+q.witnesses := by
  induction e generalizing Γ with
  | zero => simp [scalePlan,Plan.vertices,Plan.equations,Plan.witnesses]
  | succ e ih =>
      let t : Plan (.ground::Γ) :=
        .gate (.add (.var .here) (.var .here) (portRename (Renaming.weaken Γ .ground) out))
          (renamePlan (Renaming.weaken Γ .ground) q)
      have hh := ih (portRename (Renaming.weaken Γ .ground) a) (.var .here) t
      have hr := BinaryPlan.Proof.renameSize Γ (.ground::Γ) (Renaming.weaken Γ .ground) q
      simp only [t,Plan.vertices,Plan.equations,Plan.witnesses,hr.1,hr.2.1,hr.2.2] at hh
      simp only [scalePlan,Plan.vertices,Plan.equations,Plan.witnesses]
      omega

theorem exactOverhead : Targets.ExactOverhead := by
  intro Γ e a out q
  have h := plan_size e a out q
  have hc := ExistentialPlan.Proof.size Γ (scalePlan e a out q)
  exact ⟨h.1,h.2.1,h.2.2,by omega,by omega,by omega⟩
end LogicLineages.OrdinalComparison.Source.ParametricScalingPlan.Proof
