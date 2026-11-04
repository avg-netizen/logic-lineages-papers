module
public import LogicLineages.OrdinalComparison.ParametricBinaryPlanRenamingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricBinaryPlan.Proof
open GroundEquivalence PrimitiveLowering ExistentialPlan SourceAdditionCompletion BinaryPlan ParametricExistentialPlan
theorem binary_run (G : Nat → Nat) : ∀ (Γ : List Ty) (ρ : Variable Γ .ground → Nat)
    (b : BinaryDAG) (out : Port Γ) (q : Plan Γ),
    EvalWith G ρ (binaryPlan b out q) ↔ b.Run (out.value (inputs ρ)) ∧ EvalWith G ρ q := by
  intro Γ ρ b out q
  induction b generalizing Γ with
  | zero => simp [binaryPlan,EvalWith,Gate.Holds,BinaryDAG.Run,Port.value]
  | one => simp [binaryPlan,EvalWith,Gate.Holds,BinaryDAG.Run]
  | double p ih =>
      have he (x : Nat) : EvalWith G (ExistentialPlan.extend ρ x) (renamePlan (Renaming.weaken Γ .ground) q) ↔ EvalWith G ρ q :=
        rename_correct G _ _ _ _ _ (fun _ => rfl) q
      have hp (x : Nat) : (portRename (Renaming.weaken Γ .ground) out).value (inputs (ExistentialPlan.extend ρ x)) = out.value (inputs ρ) :=
        ExistentialPlan.Proof.port_rename _ _ _ (fun _ => rfl) out
      simp only [binaryPlan,EvalWith,ih,Gate.Holds,he,hp,BinaryDAG.Run,SourceAdditionCompletion.Proof.add_values]
      simp only [Port.value,inputs,SourceSortCompletion.input,ExistentialPlan.extend]
      constructor
      · rintro ⟨x,hx,ha,hq⟩
        exact ⟨⟨x,hx,ha⟩,hq⟩
      · rintro ⟨⟨x,hx,ha⟩,hq⟩
        exact ⟨x,hx,ha,hq⟩
  | doubleOne p ih =>
      have he (x z u : Nat) :
          EvalWith G (ExistentialPlan.extend (ExistentialPlan.extend (ExistentialPlan.extend ρ x) z) u)
            (renamePlan (shift 3) q) ↔ EvalWith G ρ q :=
        rename_correct G _ _ _ _ _ (fun _ => rfl) q
      have hp (x z u : Nat) :
          (portRename (shift 3) out).value
            (inputs (ExistentialPlan.extend (ExistentialPlan.extend (ExistentialPlan.extend ρ x) z) u)) = out.value (inputs ρ) :=
        ExistentialPlan.Proof.port_rename _ _ _ (fun _ => rfl) out
      simp only [binaryPlan,EvalWith,ih,Gate.Holds,he,hp,BinaryDAG.Run,SourceAdditionCompletion.Proof.add_values]
      simp only [Port.value,inputs,SourceSortCompletion.input,ExistentialPlan.extend]
      constructor
      · rintro ⟨x,z,u,hx,hz,hu,ho,hq⟩
        subst u
        exact ⟨⟨x,z,hx,hz,ho.trans (hp x z 1)⟩,hq⟩
      · rintro ⟨⟨x,z,hx,hz,ho⟩,hq⟩
        exact ⟨x,z,1,hx,hz,rfl,ho.trans (hp x z 1).symm,hq⟩


theorem run_value (b : BinaryDAG) (y : Nat) : b.Run y ↔ y=value b := by
  induction b generalizing y with
  | zero => rfl
  | one => rfl
  | double p ih =>
      simp only [BinaryDAG.Run,ih,SourceAdditionCompletion.Proof.add_values,value]
      constructor
      · rintro ⟨x,rfl,h⟩
        omega
      · intro h
        exact ⟨value p,rfl,by omega⟩
  | doubleOne p ih =>
      simp only [BinaryDAG.Run,ih,SourceAdditionCompletion.Proof.add_values,value]
      constructor
      · rintro ⟨x,z,rfl,hz,hy⟩
        omega
      · intro h
        exact ⟨value p,2*value p,rfl,by omega,by omega⟩

theorem binary_supported {Γ : List Ty} (b : BinaryDAG) (out : Port Γ) (q : Plan Γ) :
    Supported (binaryPlan b out q) ↔ Supported q := by
  induction b generalizing Γ with
  | zero => simp [binaryPlan,Supported,ParametricPrimitiveLowering.Supported]
  | one => simp [binaryPlan,Supported,ParametricPrimitiveLowering.Supported]
  | double p ih =>
      simp only [binaryPlan,Supported,ih,ParametricPrimitiveLowering.Supported,true_and,rename_supported]
  | doubleOne p ih =>
      simp only [binaryPlan,Supported,ih,ParametricPrimitiveLowering.Supported,true_and,rename_supported]

theorem exactBinaryPlan : Targets.ExactBinaryPlan := by
  refine ⟨?_,fun _ b out q => binary_supported b out q,?_⟩
  · intro G Γ ρ b out q
    rw [binary_run,run_value]
  · intro k
    exact ((run_value (binaryDAG k) k).mp (((SourceAdditionCompletion.Proof.dag_correct k).2 k).mpr rfl)).symm

theorem literal_correct (G : Nat → Nat) {Γ} (ρ : Variable Γ .ground → Nat)
    (k : Nat) (q : Plan (.ground::Γ)) :
    EvalWith G ρ (constantPlan k q) ↔ EvalWith G (ExistentialPlan.extend ρ k) q := by
  change (∃ n,EvalWith G (ExistentialPlan.extend ρ n) (binaryPlan (binaryDAG k) (.var .here) q)) ↔ _
  simp only [exactBinaryPlan.1,exactBinaryPlan.2.2,Port.value,inputs,SourceSortCompletion.input,ExistentialPlan.extend]
  simp
end LogicLineages.OrdinalComparison.Source.ParametricBinaryPlan.Proof
