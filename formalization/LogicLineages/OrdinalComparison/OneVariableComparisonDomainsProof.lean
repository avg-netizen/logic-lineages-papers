module
public import LogicLineages.OrdinalComparison.OneVariableComparisonTargets
public import LogicLineages.OrdinalComparison.ProfileHeadProof
public import LogicLineages.OrdinalComparison.PrincipalBlockDomainProof
public import LogicLineages.OrdinalComparison.Control

@[expose] public section
namespace LogicLineages.OrdinalComparison.OneVariableComparison

theorem open_lower : Targets.ActualOneVariableOpenInputLowerBound := by
  intro E hv hs x
  induction E with
  | constant c => cases hs
  | input => exact Nat.le_refl _
  | add E F ihE ihF =>
    rcases Bool.or_eq_true_iff.mp hs with hE | hF
    · have h := ihE hv.1 hE
      change x≤actualFixedLimitProfileEval E x+actualFixedLimitProfileEval F x
      omega
    · have h := ihF hv.2 hF
      change x≤actualFixedLimitProfileEval E x+actualFixedLimitProfileEval F x
      omega
  | head rho E ih =>
    exact (ih hv.2.2 hs).trans ((actualFixedLimitProfileHeads rho hv.1).2 _).le

theorem kernel_expansive : Targets.ActualSuffixKernelInputExpansive := by
  intro pi c t
  exact iterate_self_le (fun n => (self_lt_Phi n).le) (actualSuffixKernelCount pi c t) t

private theorem principal_norm (eta : NONote) :
    actualOrdinalNorm (Ordinal.omega0^eta.1.repr)=1+Vendor.R1.treeWeight eta.1 := by
  letI := eta.2
  let o : NONote := ⟨ONote.oadd eta.1 1 0,inferInstance⟩
  have h := actualOrdinalNorm_notationCorrespondence o
  simpa [o,ONote.repr,Vendor.R1.treeWeight] using h

theorem word_bound_positive (w : List (NONote × Nat)) : 1≤comparisonWordDomainBound w := by
  induction w with
  | nil => exact Nat.le_refl _
  | cons p w ih => exact ih.trans (Nat.le_max_right _ _)

theorem word_domains : Targets.ActualComparisonWordDomains := by
  intro w
  induction w with
  | nil => intro t _; exact ⟨True.intro,Nat.le_refl _⟩
  | cons p w ih =>
    intro t ht
    rcases p with ⟨eta,c⟩
    have hhead : c+1+Vendor.R1.treeWeight eta.1≤t := (Nat.le_max_left _ _).trans ht
    have htail : comparisonWordDomainBound w≤t := (Nat.le_max_right _ _).trans ht
    have hd : c+actualOrdinalNorm (Ordinal.omega0^eta.1.repr)≤t := by
      rw [principal_norm]
      omega
    have hstep := kernel_expansive (Ordinal.omega0^eta.1.repr) c t
    have hw := ih _ (htail.trans hstep)
    exact ⟨⟨hd,hw.1⟩,hstep.trans hw.2⟩

end LogicLineages.OrdinalComparison.OneVariableComparison
