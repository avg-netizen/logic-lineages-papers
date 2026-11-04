module
public import LogicLineages.OrdinalComparison.ParametricScalingPlanTargets
public import LogicLineages.OrdinalComparison.ParametricBinaryPlanProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricScalingPlan.Proof
open PrimitiveLowering ExistentialPlan BinaryPlan ParametricExistentialPlan

theorem scale_correct (G : Nat → Nat) {Γ} (ρ : Variable Γ .ground → Nat)
    (e : Nat) (a out : Port Γ) (q : Plan Γ) :
    EvalWith G ρ (scalePlan e a out q) ↔
      out.value (inputs ρ)=2^e*a.value (inputs ρ) ∧ EvalWith G ρ q := by
  induction e generalizing Γ with
  | zero => simp [scalePlan,EvalWith,Gate.Holds,eq_comm]
  | succ e ih =>
      have he (x : Nat) : EvalWith G (ExistentialPlan.extend ρ x)
          (renamePlan (Renaming.weaken Γ .ground) q) ↔ EvalWith G ρ q :=
        ParametricBinaryPlan.Proof.rename_correct G _ _ _ _ _ (fun _ => rfl) q
      have hp (x : Nat) (v : Port Γ) : (portRename (Renaming.weaken Γ .ground) v).value
          (inputs (ExistentialPlan.extend ρ x))=v.value (inputs ρ) :=
        ExistentialPlan.Proof.port_rename _ _ _ (fun _ => rfl) v
      have hpow : 2^(e+1)*a.value (inputs ρ)=2*(2^e*a.value (inputs ρ)) := by
        rw [pow_succ]
        ac_rfl
      simp only [scalePlan,EvalWith,ih,Gate.Holds,he,hp,hpow]
      simp only [Port.value,inputs,SourceSortCompletion.input,ExistentialPlan.extend]
      constructor
      · rintro ⟨x,hx,ho,hq⟩
        exact ⟨by omega,hq⟩
      · rintro ⟨ho,hq⟩
        exact ⟨2^e*a.value (inputs ρ),rfl,by
          simp only [Port.value,inputs,SourceSortCompletion.input]
          omega,hq⟩

theorem scale_supported {Γ} (e : Nat) (a out : Port Γ) (q : Plan Γ) :
    Supported (scalePlan e a out q) ↔ Supported q := by
  induction e generalizing Γ with
  | zero => simp [scalePlan,Supported,ParametricPrimitiveLowering.Supported]
  | succ e ih =>
      simp only [scalePlan,Supported,ih,ParametricPrimitiveLowering.Supported,true_and,
        ParametricBinaryPlan.Proof.rename_supported]

theorem exactScalingPlan : Targets.ExactScalingPlan :=
  ⟨fun G _ ρ e a out q => scale_correct G ρ e a out q,
    fun _ e a out q => scale_supported e a out q⟩
end LogicLineages.OrdinalComparison.Source.ParametricScalingPlan.Proof
