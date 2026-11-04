module
public import LogicLineages.OrdinalComparison.SourceBinarySpineCodeRecursionProof
public import LogicLineages.OrdinalComparison.SourceScalingSpineCodeCalibrationProof
public import LogicLineages.OrdinalComparison.SourceBinaryHalvingTraceReconstructionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceBinarySpineCode.Proof
open SourcePlanSpineCode SourcePrimitiveForestCode ExistentialPlan PrimitiveLowering BinaryPlan

theorem insert_shift {Γ} (k : Nat) (q : Plan Γ) (hq : ParametricExistentialPlan.Supported q) :
    SourcePlanInsertionCode.insert 0 k (spine q)=spine (renamePlan (shift k) q) := by
  have hr : (fun {σ} (x : Variable Γ σ) => ContextInsertionCode.insertion [] (List.replicate k .ground) Γ x)=
      (fun {σ} (x : Variable Γ σ) => shift k x) := by
    funext σ x
    induction k with
    | zero => rfl
    | succ k ih =>
      change Variable.there (SourceTypedPorts.shiftVariable (List.replicate k .ground) x)=Variable.there (shift k x)
      exact congrArg Variable.there ih
  have h := SourcePlanInsertionCode.Proof.exactSupportedInsertion [] (List.replicate k .ground) Γ q hq
  simp only [List.length_nil,List.length_replicate] at h
  rw [hr] at h
  exact h

theorem exactBitTransport : Targets.ExactBitTransport := by
  intro Γ bits base out q hq
  induction bits generalizing Γ with
  | nil =>
    by_cases hb : base=0 <;> simp [build_nil,terminal,dagOfBits,hb,binaryPlan,spine,gateInstruction,portNumber]
  | cons b bits ih =>
    by_cases hb : b=0
    · subst b
      rw [build_even,SourceScalingSpineCode.Proof.insertion_weaken q hq,SourceScalingSpineCode.Proof.port_weaken out]
      let t : Plan (.ground::Γ) := .gate (.add (.var .here) (.var .here)
        (portRename (Renaming.weaken Γ .ground) out)) (renamePlan (Renaming.weaken Γ .ground) q)
      have ht : ParametricExistentialPlan.Supported t :=
        ⟨True.intro,(ParametricBinaryPlan.Proof.rename_supported (Renaming.weaken Γ .ground) q).2 hq⟩
      have h := ih (.var .here) t ht
      simpa only [dagOfBits,List.foldr_cons,SourceBinaryHalvingTrace.wrap,ite_true,binaryPlan,spine,t,
        gateInstruction,portNumber,SourceTypedPorts.variableIndex,Nat.zero_add] using congrArg (List.cons (4,0,0,0)) h
    · rw [build_odd b hb,insert_shift 3 q hq,←SourcePrimitiveForestCode.Proof.shift_port 3 out]
      let t : Plan (.ground::.ground::.ground::Γ) :=
        .gate (.add (.var (.there (.there .here))) (.var (.there (.there .here))) (.var (.there .here)))
          (.gate (.one (.var .here))
            (.gate (.add (.var (.there .here)) (.var .here) (portRename (shift 3) out)) (renamePlan (shift 3) q)))
      have ht : ParametricExistentialPlan.Supported t :=
        ⟨True.intro,True.intro,True.intro,(ParametricBinaryPlan.Proof.rename_supported (shift 3) q).2 hq⟩
      have h := ih (.var (.there (.there .here))) t ht
      have hd : dagOfBits (b::bits) base=SourceAdditionCompletion.BinaryDAG.doubleOne (dagOfBits bits base) := by
        simp [dagOfBits,SourceBinaryHalvingTrace.wrap,hb]
      rw [hd]
      change _=(4,0,0,0)::(4,0,0,0)::(4,0,0,0)::spine (binaryPlan (dagOfBits bits base) (.var (.there (.there .here))) t)
      exact congrArg (fun xs => (4,0,0,0)::(4,0,0,0)::(4,0,0,0)::xs) h

theorem exactLiteralTransport : Targets.ExactLiteralTransport := by
  intro Γ k out q hq
  have h := exactBitTransport (SourceBinaryHalvingTrace.trace k).2.reverse
    (SourceBinaryHalvingTrace.trace k).1 out q hq
  have hd : dagOfBits (SourceBinaryHalvingTrace.trace k).2.reverse (SourceBinaryHalvingTrace.trace k).1=
      SourceAdditionCompletion.binaryDAG k := by
    unfold dagOfBits
    rw [List.foldr_reverse]
    exact SourceBinaryHalvingTrace.Proof.exactReconstruction k
  rw [hd] at h
  exact h
end LogicLineages.OrdinalComparison.Source.SourceBinarySpineCode.Proof
