module
public import LogicLineages.PermittedControl.SelectedBoundedDeltaProof

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedDeltaScalarProof
open OrdinalComparison Source SelectedSourceDomain SelectedFirstFree SelectedBoundedDelta
open Source.AdmissibleSum Source.AdmissibleAssignment

 theorem deltaScalarNorm : SelectedBoundedDeltaTargets.DeltaScalarNorm := by
  intro ctrl K hctrl Γ σ m p h hg v w hv hw ρ
  unfold LiteralCovariance.delta at hv
  cases hps : collect (m+1) (fun i => AdmissiblePartial.run p i.val (h i)) with
  | none => simp [hps] at hv
  | some ps =>
    simp only [hps,bind,pure,Option.bind_some,Option.some.injEq] at hv
    have hspec := SelectedBoundedDeltaProof.collect_success _ _ ps hps
    have hwps : w = ps 0 := Option.some.inj (hw.symm.trans (hspec 0))
    obtain ⟨q,hq,gq,wq⟩ := SelectedWeakPartialProof.partialWeakAndValid ctrl K hctrl Γ σ p 0 (h 0) (hg 0)
    have hqw : q = w := Option.some.inj (hq.symm.trans hw)
    subst q
    have hsum : 0 < ((List.ofFn h).map ordinalPartialSize).sum := by
      rw [List.ofFn_succ,List.map_cons,List.sum_cons]
      have := (actualTypedPartialSize Γ σ (h 0)).1
      omega
    have hfactor : 0 < 2^(σ.level+1)*((List.ofFn h).map ordinalPartialSize).sum :=
      Nat.mul_pos (Nat.pow_pos (by omega)) hsum
    have he := congrFun hv 0
    simp only [Fin.val_zero,↓reduceIte] at he
    rw [← he,SelectedNormSumsProof.repeatNorm ctrl Γ ρ p .scalarRepeat _ _ hfactor]
    rw [← hwps,SelectedNormSumsProof.scalarNorm ctrl Γ ρ _ (gq 0)]

 theorem fullSelectedBoundedDelta : SelectedBoundedDeltaTargets.FullSelectedBoundedDelta :=
  ⟨SelectedBoundedDeltaProof.boundedVectorSupportBridge,
    SelectedPartialNormProof.partialNormFromFreeBudget,SelectedPartialNormProof.vectorPartialNorm,
    deltaScalarNorm,SelectedBoundedDeltaProof.deltaPreservesBoundedNorm⟩

end LogicLineages.PermittedControl.SelectedDeltaScalarProof
