module
public import LogicLineages.OrdinalComparison.ScalarCarrierAccountingAccountingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ScalarCarrierAccounting.Proof

theorem actualSourceAccounting : Targets.ActualSourceAccounting := by
  intro k Γ n e
  obtain ⟨u,hu,hscalar,hpositive⟩ := AdditiveHeadTree.Proof.actualSourceTrees k
    (Ty.curriedGround (k+1) :: Γ) .here n OrdinalSyntax.defaultPolicy e
  obtain ⟨u',hu',hannotation⟩ := ActiveScalarAnnotation.Proof.actualSourceAnnotation k
    (Ty.curriedGround (k+1) :: Γ) .here n OrdinalSyntax.defaultPolicy e
  have he : u' = u := Option.some.inj (hu'.symm.trans hu)
  subst u'
  obtain ⟨xs,c,v,haccount,hv,hvalue⟩ := exactAccounting k Γ (u 0) hscalar hannotation
  exact ⟨u,xs,c,v,hu,haccount,hv,hvalue⟩
end LogicLineages.OrdinalComparison.Source.ScalarCarrierAccounting.Proof
