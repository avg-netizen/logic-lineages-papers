module
public import LogicLineages.OrdinalComparison.SourcePlanPrefixCodeTargets
public import LogicLineages.OrdinalComparison.SourcePrimitiveForestCodePortsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePlanPrefixCode.Proof
open ExistentialPlan PrimitiveLowering

theorem actualEmbedding : Targets.ActualEmbedding := by
  intro Γ q
  induction q with
  | done => exact ⟨by simp [compile,Plan.witnesses],fun _ _ => by simp [compile,Plan.witnesses]⟩
  | equation a b q ih => exact ih
  | @gate Γ g q ih =>
    constructor
    · change (List.replicate 9 Ty.ground ++ (compile q).context).length=Γ.length+(9+q.witnesses)
      simp only [List.length_append,List.length_replicate,ih.1]
      omega
    · intro τ x
      change SourceTypedPorts.variableIndex (shift 9 ((compile q).embedding x))=SourceTypedPorts.variableIndex x+(9+q.witnesses)
      rw [SourcePrimitiveForestCode.Proof.shift_index,ih.2]
      omega
  | @existsGround Γ q ih =>
    constructor
    · change (compile q).context.length=Γ.length+(1+q.witnesses)
      have hh := ih.1
      simp only [List.length_cons] at hh
      omega
    · intro τ x
      change SourceTypedPorts.variableIndex ((compile q).embedding (.there x))=SourceTypedPorts.variableIndex x+(1+q.witnesses)
      rw [ih.2]
      change SourceTypedPorts.variableIndex x+1+q.witnesses=SourceTypedPorts.variableIndex x+(1+q.witnesses)
      omega
end LogicLineages.OrdinalComparison.Source.SourcePlanPrefixCode.Proof
