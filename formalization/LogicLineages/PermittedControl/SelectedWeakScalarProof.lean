module
public import LogicLineages.PermittedControl.SelectedWeakDeltaProof
public import LogicLineages.PermittedControl.SelectedSupportProof
public import LogicLineages.PermittedControl.LiteralCovariancePartialProof

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedWeakScalarProof
open OrdinalComparison Source SelectedSourceDomain SelectedSourceSupport Source.AdmissibleSum

private theorem weakened_free {Γ : List Ty} (σ : Ty) (t : OrdinalExpression Γ) :
    ordinalHeadFree (σ := σ) (LiteralCovariance.weaken σ t) = true := by
  simp only [ordinalHeadFree,LiteralCovarianceProof.weaken_occurs,Bool.not_false]

theorem sourceWeakScalar : SelectedWeakScalarTargets.SourceWeakScalar := by
  intro ctrl B hctrl Γ σ p
  refine ⟨?_,?_,?_⟩
  · intro t ht
    obtain ⟨v,hv,gv,wv⟩ := SelectedWeakPartialProof.partialWeakAndValid ctrl B hctrl Γ σ p 0 t ht
    refine ⟨v,hv,?_⟩
    have hs := SelectedSupportProof.comparisonSupportCoverage Γ (ordinalHeadClosure t) (v 0)
    exact (SelectedSupportProof.supportComparisonBridge ctrl Γ _ _ _ hs.1 hs.2 (· ≤ ·)).mp (wv rfl)
  · intro i t ht
    obtain ⟨v,hv,gv,wv⟩ := SelectedWeakPartialProof.partialWeakAndValid ctrl B hctrl Γ σ p i t ht
    exact ⟨v,hv,fun j => ⟨gv j,weakened_free σ (v j)⟩⟩
  · intro m h hh
    obtain ⟨v,hv,gv⟩ := SelectedWeakDeltaProof.deltaValid ctrl B hctrl Γ σ m p h hh
    exact ⟨v,hv,fun j => ⟨gv j,weakened_free σ (v j)⟩⟩

theorem fullSelectedWeakScalar : SelectedWeakScalarTargets.FullSelectedWeakScalar :=
  ⟨SelectedSupportProof.evaluationIndependence,SelectedSupportProof.supportedExtension,
    SelectedSupportProof.comparisonSupportCoverage,SelectedSupportProof.supportComparisonBridge,
    SelectedWeakPartialProof.partialWeakAndValid,sourceWeakScalar⟩

end LogicLineages.PermittedControl.SelectedWeakScalarProof
