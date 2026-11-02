module
public import LogicLineages.OrdinalComparison.SelectedAccountPreparationPreparationProof
public import LogicLineages.OrdinalComparison.ScalarCarrierAccountingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SelectedAccountPreparation.Proof

theorem actualPreparedAccounting : Targets.ActualPreparedAccounting := by
  intro k left right n e
  obtain ⟨u,hu,ht,hpositive⟩ := AdditiveHeadTree.Proof.actualSourceTrees k
    (left ++ Ty.curriedGround (k+1) :: right)
    (SelectedBinder.selected left right (Ty.curriedGround (k+1))) n OrdinalSyntax.defaultPolicy e
  obtain ⟨u',hu',ha⟩ := ActiveScalarAnnotation.Proof.actualSourceAnnotation k
    (left ++ Ty.curriedGround (k+1) :: right)
    (SelectedBinder.selected left right (Ty.curriedGround (k+1))) n OrdinalSyntax.defaultPolicy e
  have he : u' = u := Option.some.inj (hu'.symm.trans hu)
  subst u'
  have hc := selectedCertificates k left right OrdinalSyntax.defaultPolicy (u 0)
  obtain ⟨xs,c,v,haccount,hv,hvalue⟩ := ScalarCarrierAccounting.Proof.exactAccounting k (left ++ right)
    (prepare left right (Ty.curriedGround (k+1)) (u 0)) (hc.2.1 ht) (hc.2.2 ha)
  refine ⟨u,xs,c,v,hu,?_,haccount,hv,hvalue⟩
  rw [prepareSource,SourceRenaming.Proof.assignmentNaturality,hu]
  rfl
end LogicLineages.OrdinalComparison.Source.SelectedAccountPreparation.Proof
