module
public import LogicLineages.OrdinalComparison.SourceScalingSpineCodeTargets
public import LogicLineages.OrdinalComparison.SourcePlanInsertionCodeCalibrationProof
public import LogicLineages.OrdinalComparison.ParametricBinaryPlanRenamingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceScalingSpineCode.Proof
open SourcePlanSpineCode SourcePrimitiveForestCode ExistentialPlan PrimitiveLowering BinaryPlan

theorem build_zero (a out : Nat) (is : List Instruction) : build 0 a out is=(1,a,out,0)::is := rfl
theorem build_succ (e a out : Nat) (is : List Instruction) :
    build (e+1) a out is=(4,0,0,0)::build e (shiftPort 1 a) 1
      ((2,1,1,shiftPort 1 out)::SourcePlanInsertionCode.insert 0 1 is) := by
  simp only [build,Function.iterate_succ_apply,List.replicate_succ,List.cons_append,advance]

theorem exactNumericRecursion : Targets.ExactNumericRecursion := ⟨build_zero,build_succ⟩

theorem insertion_weaken {Γ} (q : Plan Γ) (hq : ParametricExistentialPlan.Supported q) :
    SourcePlanInsertionCode.insert 0 1 (spine q)=spine (renamePlan (Renaming.weaken Γ .ground) q) := by
  have h := SourcePlanInsertionCode.Proof.exactSupportedInsertion [] [.ground] Γ q hq
  exact h

theorem port_weaken {Γ} (a : Port Γ) :
    shiftPort 1 (portNumber a)=portNumber (portRename (Renaming.weaken Γ .ground) a) := by
  cases a with
  | zero => rfl
  | var x => simp [shiftPort,portNumber,portRename,Renaming.weaken,SourceTypedPorts.variableIndex]

theorem exactScaling : Targets.ExactScaling := by
  intro Γ e a out q hq
  induction e generalizing Γ with
  | zero => rfl
  | succ e ih =>
    rw [build_succ,insertion_weaken q hq,port_weaken a,port_weaken out]
    let t : Plan (.ground::Γ) := .gate (.add (.var .here) (.var .here)
      (portRename (Renaming.weaken Γ .ground) out)) (renamePlan (Renaming.weaken Γ .ground) q)
    have ht : ParametricExistentialPlan.Supported t :=
      ⟨True.intro,(ParametricBinaryPlan.Proof.rename_supported (Renaming.weaken Γ .ground) q).2 hq⟩
    have h := ih (portRename (Renaming.weaken Γ .ground) a) (.var .here) t ht
    simpa only [ParametricScalingPlan.scalePlan,spine,t,gateInstruction,portNumber,SourceTypedPorts.variableIndex,Nat.zero_add] using congrArg (List.cons (4,0,0,0)) h
end LogicLineages.OrdinalComparison.Source.SourceScalingSpineCode.Proof
