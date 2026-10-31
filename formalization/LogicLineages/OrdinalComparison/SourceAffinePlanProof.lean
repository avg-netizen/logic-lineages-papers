module
public import LogicLineages.OrdinalComparison.SourceAffinePlanTargets
public import LogicLineages.OrdinalComparison.SourceBinaryPlanProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AffinePlan.Proof
open PrimitiveLowering ExistentialPlan

theorem port_weaken {Γ} (ρ : Variable Γ .ground → Nat) (n : Nat) (a : Port Γ) :
    (portRename (Renaming.weaken Γ .ground) a).value (inputs (ExistentialPlan.extend ρ n))=a.value (inputs ρ) :=
  ExistentialPlan.Proof.port_rename _ _ _ (fun _ => rfl) a

theorem addBind : Targets.AddBind := by
  intro Γ ρ a b q
  simp only [AffinePlan.addBind,Eval,Gate.Holds,SourceAdditionCompletion.Proof.add_values,port_weaken]
  simp only [Port.value,inputs,SourceSortCompletion.input,ExistentialPlan.extend]
  constructor
  · rintro ⟨n,he,hq⟩
    subst n
    exact hq
  · intro hq
    exact ⟨_,rfl,hq⟩

theorem multiply : Targets.Multiply := by
  intro Γ ρ p a out q
  induction p generalizing Γ with
  | zero => simp [mulPlan,Eval,Gate.Holds,Port.value,eq_comm]
  | succ p ih =>
    have he (n : Nat) : Eval (ExistentialPlan.extend ρ n) (BinaryPlan.renamePlan (Renaming.weaken Γ .ground) q) ↔ Eval ρ q :=
      BinaryPlan.Proof.renameCorrect _ _ _ _ _ (fun _ => rfl) q
    simp only [mulPlan,Eval,ih,Gate.Holds,SourceAdditionCompletion.Proof.add_values,port_weaken,he]
    simp only [Port.value,inputs,SourceSortCompletion.input,ExistentialPlan.extend]
    constructor
    · rintro ⟨n,hn,ha,hq⟩
      exact ⟨by rw [Nat.succ_mul,hn]; exact ha,hq⟩
    · rintro ⟨ha,hq⟩
      exact ⟨_,rfl,by simpa only [Nat.succ_mul] using ha,hq⟩

theorem multiplySize : Targets.MultiplySize := by
  intro Γ p a out q
  induction p generalizing Γ with
  | zero => simp [mulPlan,Plan.vertices,Plan.equations,Plan.witnesses]
  | succ p ih =>
    let t : Plan (.ground::Γ) := .gate (.add (.var .here)
      (portRename (Renaming.weaken Γ .ground) a) (portRename (Renaming.weaken Γ .ground) out))
      (BinaryPlan.renamePlan (Renaming.weaken Γ .ground) q)
    have hh := ih (Γ:=.ground::Γ) (portRename (Renaming.weaken Γ .ground) a) (.var .here) t
    have hr := BinaryPlan.Proof.renameSize Γ (.ground::Γ) (Renaming.weaken Γ .ground) q
    simp only [t,Plan.vertices,Plan.equations,Plan.witnesses,hr.1,hr.2.1,hr.2.2] at hh
    simp only [mulPlan,Plan.vertices,Plan.equations,Plan.witnesses]
    constructor
    · omega
    constructor <;> omega

theorem multiplyBind : Targets.MultiplyBind := by
  intro Γ ρ p a q
  have hm (n : Nat) := multiply (.ground::Γ) (ExistentialPlan.extend ρ n) p (portRename (Renaming.weaken Γ .ground) a) (.var .here) q
  simp only [mulBind,Eval,hm,port_weaken]
  simp only [Port.value,inputs,SourceSortCompletion.input,ExistentialPlan.extend]
  constructor
  · rintro ⟨n,he,hq⟩
    subst n
    exact hq
  · intro hq
    exact ⟨_,rfl,hq⟩

theorem affine : Targets.Affine := by
  intro Γ ρ p c a x y
  unfold affinePlan
  rw [multiplyBind,addBind,BinaryPlan.Proof.literalCorrect,addBind]
  simp only [Eval,Gate.Holds]
  simp only [port_weaken]
  cases y <;> simp [portRename,shift,Port.value,inputs,SourceSortCompletion.input,ExistentialPlan.extend]
end LogicLineages.OrdinalComparison.Source.AffinePlan.Proof
