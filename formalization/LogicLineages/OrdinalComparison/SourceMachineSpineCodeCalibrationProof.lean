module
public import LogicLineages.OrdinalComparison.SourceMachineSpineCodeTargets
public import LogicLineages.OrdinalComparison.SourceBinarySpineCodeCalibrationProof
public import LogicLineages.OrdinalComparison.SourceMachineConjunctionPlanSemanticProof
public import LogicLineages.OrdinalComparison.SourcePrimitiveForestCodePortsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineSpineCode.Proof
open SourcePlanSpineCode SourcePrimitiveForestCode ExistentialPlan PrimitiveLowering BinaryPlan
open SourceMachineConjunctionPlan (Base Wired port)

private theorem port_index (i : Fin 13) : portNumber (port i)=i.val+1 := by
  change SourceTypedPorts.variableIndex (fresh (Γ:=[]) i)+1=i.val+1
  rw [SourcePrimitiveForestCode.Proof.fresh_index]

private def restPlan : Plan Wired :=
  .gate (.add (port 10) (port 7) (port 3))
    (.gate (.eq (port 3) (port 2))
      (.gate (.add (port 12) (port 12) (port 4))
        (.gate (.add (port 4) (port 6) (port 5))
          (.gate (.eq (port 11) (port 5))
            (.equation (Expr.successor (port 10)).graph (Expr.port (port 11)).graph .done)))))
private theorem rest_supported : ParametricExistentialPlan.Supported restPlan := by
  simp [restPlan,ParametricExistentialPlan.Supported,ParametricPrimitiveLowering.Supported]
private theorem rest_code : remainder=spine restPlan := by
  have hs := (SourcePrimitiveForestCode.Proof.exactExpressions Wired (.successor (port 10))).2
  have hp := (SourcePrimitiveForestCode.Proof.exactExpressions Wired (.port (port 11))).2
  simp only [expressionCode,port_index] at hs hp
  simp only [remainder,restPlan,spine,gateInstruction,port_index]
  rw [←hs,←hp]
  norm_num

theorem tail_correct (e : Nat) : tail e=spine (SourceMachineConjunctionPlan.tail e) := by
  have h := SourceScalingSpineCode.Proof.exactScaling e (port 1) (port 2) restPlan rest_supported
  simp only [port_index] at h
  norm_num at h
  unfold tail
  rw [rest_code,h]
  rfl

private theorem tail_supported (e : Nat) : ParametricExistentialPlan.Supported (SourceMachineConjunctionPlan.tail e) := by
  change True ∧ True ∧ ParametricExistentialPlan.Supported (ParametricScalingPlan.scalePlan e (port 1) (port 2) restPlan)
  exact ⟨True.intro,True.intro,(ParametricScalingPlan.Proof.scale_supported e (port 1) (port 2) restPlan).2 rest_supported⟩

theorem constant_correct {Γ} (k : Nat) (q : Plan (.ground::Γ)) (hq : ParametricExistentialPlan.Supported q) :
    constant k (spine q)=spine (constantPlan k q) := by
  change (4,0,0,0)::SourceBinarySpineCode.build k 1 (spine q)=
    (4,0,0,0)::spine (binaryPlan (SourceAdditionCompletion.binaryDAG k) (.var .here) q)
  apply congrArg (List.cons (4,0,0,0))
  exact SourceBinarySpineCode.Proof.exactLiteralTransport k (.var .here) q hq

private theorem constant_supported {Γ} (k : Nat) (q : Plan (.ground::Γ)) (hq : ParametricExistentialPlan.Supported q) :
    ParametricExistentialPlan.Supported (constantPlan k q) :=
  (ParametricBinaryPlan.Proof.binary_supported (SourceAdditionCompletion.binaryDAG k) (.var .here) q).2 hq

theorem exactSpine : Targets.ExactSpine := by
  intro b e
  refine ⟨?_,SourceMachineConjunctionPlan.Proof.supportedSyntax b e⟩
  unfold code
  rw [tail_correct]
  let q : Plan (.ground::.ground::.ground::Base) :=
    .existsGround (.existsGround (.existsGround (.existsGround (.existsGround (.existsGround (SourceMachineConjunctionPlan.tail e))))))
  have hq : ParametricExistentialPlan.Supported q := tail_supported e
  change constant (2*b+5) (constant 4 (constant 1 (spine q)))=spine (SourceMachineConjunctionPlan.plan b e)
  rw [constant_correct 1 q hq,constant_correct 4 (constantPlan 1 q) (constant_supported 1 q hq),
    constant_correct (2*b+5) (constantPlan 4 (constantPlan 1 q)) (constant_supported 4 _ (constant_supported 1 q hq))]
  rfl
end LogicLineages.OrdinalComparison.Source.SourceMachineSpineCode.Proof
