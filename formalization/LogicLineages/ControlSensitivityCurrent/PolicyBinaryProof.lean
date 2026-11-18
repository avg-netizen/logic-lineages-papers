module
public import LogicLineages.ControlSensitivityCurrent.PolicyBinaryTargets
public import LogicLineages.ControlSensitivityCurrent.PolicyPlanSemanticProof
public import LogicLineages.OrdinalComparison.SourceAdditionCompletionStatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyBinary
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open BinaryPlan
open GroundEquivalence PrimitiveLowering ExistentialPlan SourceAdditionCompletion

theorem renameCorrect : PolicyBinaryTargets.Rename := by
  intro pol f Γ Δ r ρ ν h q
  induction q generalizing Δ with
  | done => rfl
  | equation a b q ih =>
      simp only [renamePlan,PolicyPlan.Eval]
      apply and_congr
      · exact PolicyPlan.equation_dag_rename pol f r ρ ν h a b
      · apply ih
        exact h
  | gate g q ih =>
      simp only [renamePlan,PolicyPlan.Eval]
      apply and_congr
      · exact PolicyPlan.gate_rename r ρ ν h g
      · apply ih
        exact h
  | existsGround q ih =>
      simp only [renamePlan,PolicyPlan.Eval]
      apply exists_congr
      intro x
      apply ih
      intro y
      cases y with
      | here => rfl
      | there y => exact h y

theorem renameSize : BinaryPlan.Targets.RenameSize := by
  intro Γ Δ r q
  induction q generalizing Δ with
  | done => exact ⟨rfl,rfl,rfl⟩
  | equation a b q ih =>
      obtain ⟨hv,he,hw⟩ := ih Δ r
      simp only [renamePlan,Plan.vertices,Plan.equations,Plan.witnesses,ScopedDAG.renameInput,hv,he,hw]
      trivial
  | gate g q ih =>
      obtain ⟨hv,he,hw⟩ := ih Δ r
      simp only [renamePlan,Plan.vertices,Plan.equations,Plan.witnesses,hv,he,hw]
      trivial
  | existsGround q ih =>
      obtain ⟨hv,he,hw⟩ := ih (.ground::Δ) (Renaming.lift r)
      simp only [renamePlan,Plan.vertices,Plan.equations,Plan.witnesses,hv,he,hw]
      trivial

theorem binaryCorrect : PolicyBinaryTargets.Binary := by
  intro pol f Γ ρ b out q
  induction b generalizing Γ with
  | zero => simp [binaryPlan,PolicyPlan.Eval,Gate.Holds,BinaryDAG.Run,Port.value]
  | one => simp [binaryPlan,PolicyPlan.Eval,Gate.Holds,BinaryDAG.Run]
  | double p ih =>
      have he (x : Nat) : PolicyPlan.Eval pol f (ExistentialPlan.extend ρ x) (renamePlan (Renaming.weaken Γ .ground) q) ↔ PolicyPlan.Eval pol f ρ q :=
        renameCorrect pol f _ _ _ _ _ (fun _ => rfl) q
      have hp (x : Nat) : (portRename (Renaming.weaken Γ .ground) out).value (inputs (ExistentialPlan.extend ρ x)) = out.value (inputs ρ) :=
        PolicyPlan.port_rename _ _ _ (fun _ => rfl) out
      simp only [binaryPlan,PolicyPlan.Eval,ih,Gate.Holds,he,hp,BinaryDAG.Run,SourceAdditionCompletion.Proof.add_values]
      simp only [Port.value,inputs,SourceSortCompletion.input,ExistentialPlan.extend]
      constructor
      · rintro ⟨x,hx,ha,hq⟩
        exact ⟨⟨x,hx,ha⟩,hq⟩
      · rintro ⟨⟨x,hx,ha⟩,hq⟩
        exact ⟨x,hx,ha,hq⟩
  | doubleOne p ih =>
      have he (x z u : Nat) :
          PolicyPlan.Eval pol f (ExistentialPlan.extend (ExistentialPlan.extend (ExistentialPlan.extend ρ x) z) u)
            (renamePlan (shift 3) q) ↔ PolicyPlan.Eval pol f ρ q :=
        renameCorrect pol f _ _ _ _ _ (fun _ => rfl) q
      have hp (x z u : Nat) :
          (portRename (shift 3) out).value
            (inputs (ExistentialPlan.extend (ExistentialPlan.extend (ExistentialPlan.extend ρ x) z) u)) = out.value (inputs ρ) :=
        PolicyPlan.port_rename _ _ _ (fun _ => rfl) out
      simp only [binaryPlan,PolicyPlan.Eval,ih,Gate.Holds,he,hp,BinaryDAG.Run,SourceAdditionCompletion.Proof.add_values]
      simp only [Port.value,inputs,SourceSortCompletion.input,ExistentialPlan.extend]
      constructor
      · rintro ⟨x,z,u,hx,hz,hu,ho,hq⟩
        subst u
        exact ⟨⟨x,z,hx,hz,ho.trans (hp x z 1)⟩,hq⟩
      · rintro ⟨⟨x,z,hx,hz,ho⟩,hq⟩
        exact ⟨x,z,1,hx,hz,rfl,ho.trans (hp x z 1).symm,hq⟩

theorem binarySize : BinaryPlan.Targets.BinarySize := by
  intro Γ b out q
  induction b generalizing Γ with
  | zero => simp [binaryPlan,Plan.vertices,Plan.equations,Plan.witnesses,BinaryDAG.gates]
  | one => simp [binaryPlan,Plan.vertices,Plan.equations,Plan.witnesses,BinaryDAG.gates]
  | double p ih =>
      let t : Plan (.ground::Γ) :=
        .gate (.add (.var .here) (.var .here) (portRename (Renaming.weaken Γ .ground) out))
          (renamePlan (Renaming.weaken Γ .ground) q)
      have hh := ih (Γ := .ground::Γ) (.var .here) t
      have hr := renameSize Γ (.ground::Γ) (Renaming.weaken Γ .ground) q
      simp only [t,Plan.vertices,Plan.equations,Plan.witnesses,hr.1,hr.2.1,hr.2.2] at hh
      simp only [binaryPlan,Plan.vertices,Plan.equations,Plan.witnesses,BinaryDAG.gates]
      constructor
      · omega
      constructor <;> omega
  | doubleOne p ih =>
      let t : Plan (.ground::.ground::.ground::Γ) :=
        .gate (.add (.var (.there (.there .here))) (.var (.there (.there .here))) (.var (.there .here)))
          (.gate (.one (.var .here))
            (.gate (.add (.var (.there .here)) (.var .here) (portRename (shift 3) out))
              (renamePlan (shift 3) q)))
      have hh := ih (Γ := .ground::.ground::.ground::Γ) (.var (.there (.there .here))) t
      have hr := renameSize Γ (.ground::.ground::.ground::Γ) (shift 3) q
      simp only [t,Plan.vertices,Plan.equations,Plan.witnesses,hr.1,hr.2.1,hr.2.2] at hh
      simp only [binaryPlan,Plan.vertices,Plan.equations,Plan.witnesses,BinaryDAG.gates]
      constructor
      · omega
      constructor <;> omega

theorem literalCorrect : PolicyBinaryTargets.Literal := by
  intro pol f Γ ρ k q
  change (∃ n, PolicyPlan.Eval pol f (ExistentialPlan.extend ρ n) (binaryPlan (binaryDAG k) (.var .here) q)) ↔ _
  constructor
  · rintro ⟨n,hn⟩
    have hb := (binaryCorrect pol f (.ground::Γ) (ExistentialPlan.extend ρ n) (binaryDAG k) (.var .here) q).mp hn
    have he : n=k := ((SourceAdditionCompletion.Proof.dag_correct k).2 n).mp hb.1
    subst n
    exact hb.2
  · intro hq
    refine ⟨k,?_⟩
    apply (binaryCorrect pol f (.ground::Γ) (ExistentialPlan.extend ρ k) (binaryDAG k) (.var .here) q).mpr
    exact ⟨((SourceAdditionCompletion.Proof.dag_correct k).2 k).mpr rfl,hq⟩

theorem literalSize : BinaryPlan.Targets.LiteralSize := by
  intro Γ k q
  have hb := binarySize (.ground::Γ) (binaryDAG k) (.var .here) q
  have hg := (SourceAdditionCompletion.Proof.dag_correct k).1
  simp only [constantPlan,Plan.vertices,Plan.equations,Plan.witnesses]
  constructor
  · omega
  constructor <;> omega
theorem actualCounts : PolicyBinaryTargets.ActualCounts :=
  ⟨renameSize,binarySize,literalSize⟩
end LogicLineages.ControlSensitivityCurrent.PolicyBinary
