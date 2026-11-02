module
public import LogicLineages.OrdinalComparison.AccountSemanticDeterminacyDeterminacyProof
public import LogicLineages.OrdinalComparison.ScalarCarrierAccountingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AccountSemanticDeterminacy.Proof
open ScalarCarrierAccounting

theorem carrierSum_trace (xs : List Carrier) :
    carrierSum xs = (headValues xs).foldr ordinalNaturalSum 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change ordinalNaturalSum x.head (carrierSum xs) =
      ordinalNaturalSum x.head ((headValues xs).foldr ordinalNaturalSum 0)
    rw [ih]

theorem carrierSum_congr {xs ys : List Carrier} (he : headValues xs = headValues ys) :
    carrierSum xs = carrierSum ys := by
  rw [carrierSum_trace,carrierSum_trace,he]

theorem universalSoundness : Targets.UniversalSoundness := by
  intro k Γ q xs c v ht ha haccount hv
  obtain ⟨ys,d,w,hchosen,hw,hvalue⟩ := ScalarCarrierAccounting.Proof.exactAccounting k Γ q ht ha
  obtain ⟨htrace,hcd,hlen,hreserve⟩ := accountingDeterminacy k Γ q xs ys c d haccount hchosen
  have hwv : w = v := Option.some.inj (hw.symm.trans hv)
  subst w
  subst d
  have hsum := carrierSum_congr htrace
  intro μ
  exact (hvalue μ).trans (congrArg (fun x => x + (c : Ordinal)) hsum.symm)

theorem actualSourceSoundness : Targets.ActualSourceSoundness := by
  intro k Γ n e
  obtain ⟨u,hu,ht,hpositive⟩ := AdditiveHeadTree.Proof.actualSourceTrees k
    (Ty.curriedGround (k+1) :: Γ) .here n OrdinalSyntax.defaultPolicy e
  obtain ⟨u',hu',ha⟩ := ActiveScalarAnnotation.Proof.actualSourceAnnotation k
    (Ty.curriedGround (k+1) :: Γ) .here n OrdinalSyntax.defaultPolicy e
  have he : u' = u := Option.some.inj (hu'.symm.trans hu)
  subst u'
  obtain ⟨xs,c,v,haccount,hv,hvalue⟩ := ScalarCarrierAccounting.Proof.exactAccounting k Γ (u 0) ht ha
  refine ⟨u,v,hu,hv,⟨xs,c,haccount⟩,?_⟩
  intro ys d hy
  exact universalSoundness k Γ (u 0) ys d v ht ha hy hv
end LogicLineages.OrdinalComparison.Source.AccountSemanticDeterminacy.Proof
