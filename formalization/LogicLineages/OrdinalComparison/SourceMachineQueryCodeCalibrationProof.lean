module
public import LogicLineages.OrdinalComparison.SourceMachineQueryCodeTargets
public import LogicLineages.OrdinalComparison.SourceMachineSpineCodeProof
public import LogicLineages.OrdinalComparison.SourceMachineRawValuationsCoordinatesProof
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineQueryCode.Proof
open ExistentialPlan

theorem roundtrip (q : Query) : unpack (pack q)=some q := Encodable.encodek q

theorem exactPackaging : Targets.ExactPackaging := by
  refine ⟨roundtrip,?_⟩
  intro b e
  constructor
  · have ho := SourceMachineSpineCode.Proof.exactOutputs b e
    have hl := (SourcePlanPrefixCode.Proof.actualEmbedding SourceMachineConjunctionPlan.Base (SourceMachineConjunctionPlan.plan b e)).1
    simp only [SourceMachineConjunctionPlan.Base,List.length_replicate] at hl
    unfold request
    rw [ho.1,ho.2,hl]
  · exact roundtrip (request b e)

theorem ground_codes (Γ : List Ty) (hg : SourceMachineRawValuations.AllGround Γ) :
    Γ.map SyntaxCode.typeCode=List.replicate Γ.length (SyntaxCode.typeCode Ty.ground) := by
  induction Γ with
  | nil => rfl
  | cons σ Γ ih =>
    have hσ := hg σ (List.mem_cons_self)
    have ht : SourceMachineRawValuations.AllGround Γ := fun τ h => hg τ (List.mem_cons_of_mem _ h)
    simp only [List.map_cons,List.length_cons,List.replicate_succ,hσ,ih ht]

theorem generatedSourceValidity : Targets.GeneratedSourceValidity := by
  intro b e
  rw [(exactPackaging.2 b e).1]
  let q := SourceMachineConjunctionPlan.plan b e
  let es := (compile q).forest.map (fun p => (p.1.term,p.2.term))
  let a := SourceAggregateCompletion.aggregate es
  have hg := SourceMachineRawValuations.Proof.groundContexts.2 b e
  have hr := (SyntaxCode.Proof.typedCheckExact (compile q).context Ty.ground (SyntaxCode.encodeTerm a.2)).2 ⟨a.2,rfl⟩
  have hl := (SyntaxCode.Proof.typedCheckExact (compile q).context Ty.ground (SyntaxCode.encodeTerm a.1)).2 ⟨a.1,rfl⟩
  rw [ground_codes (compile q).context hg] at hr hl
  exact ⟨hr,hl⟩
end LogicLineages.OrdinalComparison.Source.SourceMachineQueryCode.Proof
