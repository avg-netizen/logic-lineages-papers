module
public import LogicLineages.OrdinalComparison.NumericAccountDataSemanticProof
public import LogicLineages.OrdinalComparison.NumericAccountDataPrimitiveProof
public import LogicLineages.OrdinalComparison.CanonicalAnnotationBuilderCodeProof
public import LogicLineages.OrdinalComparison.DeterministicAccountDataProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.NumericAccountData.Proof

theorem actualCanonicalSource : Targets.ActualCanonicalSource := by
  intro k Γ n e
  obtain ⟨u,d,hb,hu,he,hd⟩ := CanonicalAnnotationBuilderCode.Proof.actualSourceBuild k _ .here n e
  simp only [SourceTypedPorts.variableIndex] at hb
  obtain ⟨rs,c,labels,ha,hm,haccount⟩ := DeterministicAccountData.Proof.exactDataAccounting k Γ d hd
  refine ⟨u,rs,c,labels,?_,hu,hm,?_⟩
  · unfold sourceAccountCode
    change (CanonicalAnnotationBuilderCode.buildCode _ 0 _ >>= _) = _
    rw [hb]
    change ((accountCode ((Ty.curriedGround (k+1)::Γ).map SyntaxCode.typeCode)
      (SourceAnnotationCode.code d)).bind (fun p => some (OrdinalSyntax.vectorCode u,p.1,p.2))) = _
    rw [exactNumericAccounting,ha]
    rfl
  · simpa only [he] using haccount
end LogicLineages.OrdinalComparison.Source.NumericAccountData.Proof
