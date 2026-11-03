module
public import LogicLineages.OrdinalComparison.GroundPartialCarrierTransportGeneralProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundPartialCarrierTransport.Proof

theorem actualSourceGroundPartial : Targets.ActualSourceGroundPartial := by
  intro k left right n e
  obtain ⟨u,xs,c,oldPart,hu,hprepared,haccount,hold,hvalue⟩ :=
    SelectedAccountPreparation.Proof.actualPreparedAccounting k (Ty.ground :: left) right n e
  obtain ⟨u',hu',ht,hpositive⟩ := AdditiveHeadTree.Proof.actualSourceTrees k
    ((Ty.ground :: left) ++ Ty.curriedGround (k+1) :: right)
    (SelectedBinder.selected (Ty.ground :: left) right (Ty.curriedGround (k+1)))
    n OrdinalSyntax.defaultPolicy e
  have heu : u' = u := Option.some.inj (hu'.symm.trans hu)
  subst u'
  obtain ⟨u'',hu'',ha⟩ := ActiveScalarAnnotation.Proof.actualSourceAnnotation k
    ((Ty.ground :: left) ++ Ty.curriedGround (k+1) :: right)
    (SelectedBinder.selected (Ty.ground :: left) right (Ty.curriedGround (k+1)))
    n OrdinalSyntax.defaultPolicy e
  have heu' : u'' = u := Option.some.inj (hu''.symm.trans hu)
  subst u''
  obtain ⟨v,c',hv,hnew,hcc,hreserve⟩ := groundPartialAccount k left right (u 0) xs c ht ha haccount
  have hvtrees := AdditiveHeadTree.Proof.groundPartialTrees k
    (left ++ Ty.curriedGround (k+1) :: right)
    (SelectedBinder.selected left right (Ty.curriedGround (k+1)))
    OrdinalSyntax.defaultPolicy (u 0) v ht hv
  have hvannotation := ActiveScalarAnnotation.Proof.groundPartialTransport k
    (left ++ Ty.curriedGround (k+1) :: right)
    (SelectedBinder.selected left right (Ty.curriedGround (k+1)))
    OrdinalSyntax.defaultPolicy (u 0) v ha hv
  have hselected := SelectedAccountPreparation.Proof.selectedCertificates k left right OrdinalSyntax.defaultPolicy (v 0)
  have htree := hselected.2.1 hvtrees.1
  have hann := hselected.2.2 hvannotation
  obtain ⟨ys,d,newPart,hy,hnewrun,hchosen⟩ := ScalarCarrierAccounting.Proof.exactAccounting k (left ++ right)
    (after k left right (v 0)) htree hann
  have hsound := AccountSemanticDeterminacy.Proof.universalSoundness k (left ++ right)
    (after k left right (v 0)) xs c' newPart htree hann hnew hnewrun
  refine ⟨u,xs,c,v,c',oldPart,newPart,hu,hprepared,haccount,hv,hnew,hcc,hreserve,hold,hnewrun,?_⟩
  intro μold μnew
  exact ⟨hvalue μold,hsound μnew⟩
end LogicLineages.OrdinalComparison.Source.GroundPartialCarrierTransport.Proof
