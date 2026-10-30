module
public import LogicLineages.OrdinalComparison.KernelSuccessorNormalizeTargets
public import LogicLineages.OrdinalComparison.SuccessorKernelsProof
public import LogicLineages.OrdinalComparison.OptimizedMaximumGreedyProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem normalize_power_norm (eta : NONote) :
    actualOrdinalNorm (Ordinal.omega0^eta.1.repr)=1+Vendor.R1.treeWeight eta.1 := by
  have h := (actualCNFBlock eta.1.repr 0 (normalRepresentationSound eta)
    (Ordinal.opow_pos _ Ordinal.omega0_pos) 1).2.1
  have hz : actualOrdinalNorm (0 : Ordinal)=0 := actualOrdinalNorm_notationCorrespondence (0 : NONote)
  simpa only [PNat.one_coe,Nat.cast_one,mul_one,add_zero,Nat.one_mul,hz,
    Nat.add_zero,actualOrdinalNorm_notationCorrespondence eta] using h

private theorem normalize_raw_def {eta mu : ONote} {c : Nat} {x}
    (hf : ONote.fundamentalSequence eta=x) :
    rawKernelSuccessorNormalize eta mu c =
      if ONote.cmp eta mu ≠ Ordering.gt then ([(eta,c)],c+1+Vendor.R1.treeWeight eta)
      else match (motive := (x : Option ONote ⊕ (Nat → ONote)) → ONote.FundamentalSequenceProp eta x → List (ONote × Nat) × Nat)
        x, hf ▸ ONote.fundamentalSequence_has_prop eta with
      | Sum.inl none, _ => ([(eta,c)],c+1+Vendor.R1.treeWeight eta)
      | Sum.inl (some pred), _ =>
        let child := rawKernelSuccessorNormalize pred mu c
        ((eta,c+(1+Vendor.R1.treeWeight pred))::child.1,
          max (c+(1+Vendor.R1.treeWeight pred)+(1+Vendor.R1.treeWeight eta)) child.2)
      | Sum.inr _, _ => ([(eta,c)],c+1+Vendor.R1.treeWeight eta) := by
  subst x
  rw [rawKernelSuccessorNormalize]
  rfl

private theorem normalize_stop (eta mu : NONote) (c : Nat)
    (h : ONote.cmp eta.1 mu.1 ≠ Ordering.gt) :
    kernelSuccessorNormalize eta mu c=([(eta.1,c)],c+1+Vendor.R1.treeWeight eta.1) := by
  change rawKernelSuccessorNormalize eta.1 mu.1 c=_
  rw [rawKernelSuccessorNormalize]
  simp only [if_pos h]

private theorem normalize_cmp_gt (eta mu : NONote)
    (h : ONote.cmp eta.1 mu.1=Ordering.gt) : mu.1.repr<eta.1.repr := by
  have hh := ONote.cmp_compares eta.1 mu.1
  rw [h] at hh
  exact hh

private theorem normalize_stop_eq (eta mu : NONote) (hle : mu.1.repr≤eta.1.repr)
    (h : ONote.cmp eta.1 mu.1 ≠ Ordering.gt) : eta.1.repr=mu.1.repr := by
  have hh := ONote.cmp_compares eta.1 mu.1
  cases hc : ONote.cmp eta.1 mu.1 with
  | lt =>
    rw [hc] at hh
    exact (not_lt_of_ge hle hh).elim
  | eq =>
    rw [hc] at hh
    exact congrArg ONote.repr hh
  | gt => exact (h hc).elim

theorem actualKernelSuccessorNormalizeStructure : Targets.ActualKernelSuccessorNormalizeStructure := by
  intro eta
  induction eta using NONote.lt_wf.induction with
  | h eta ih =>
    intro mu hp hle c
    by_cases hstop : ONote.cmp eta.1 mu.1 ≠ Ordering.gt
    · have heq := normalize_stop_eq eta mu hle hstop
      rw [normalize_stop eta mu c hstop]
      refine ⟨by simp,?_,[],eta.1,by simp,Or.inl heq⟩
      intro p hm
      simp only [List.mem_singleton] at hm
      subst p
      exact ⟨eta.2,hle,le_rfl⟩
    · have hgt : ONote.cmp eta.1 mu.1=Ordering.gt := by tauto
      have hlt := normalize_cmp_gt eta mu hgt
      have hprop := ONote.fundamentalSequence_has_prop eta.1
      cases hf : ONote.fundamentalSequence eta.1 with
      | inl x =>
        cases x with
        | none =>
          rw [hf] at hprop
          have hz : eta.1=0 := hprop
          have hzero : eta.1.repr=0 := by rw [hz]; rfl
          rw [hzero] at hlt
          exact (not_lt_of_ge hp.le hlt).elim
        | some a =>
          rw [hf] at hprop
          let pred : NONote := ⟨a,hprop.2 eta.2⟩
          have hsmall : pred<eta := by
            change a.repr<eta.1.repr
            rw [hprop.1]
            exact Order.lt_succ _
          have hchild : mu.1.repr≤pred.1.repr := by
            rw [hprop.1] at hlt
            exact Order.lt_succ_iff.mp hlt
          have hi := ih pred hsmall mu hp hchild c
          have heq : kernelSuccessorNormalize eta mu c=
              ((eta.1,c+(1+Vendor.R1.treeWeight pred.1))::(kernelSuccessorNormalize pred mu c).1,
                max (c+(1+Vendor.R1.treeWeight pred.1)+(1+Vendor.R1.treeWeight eta.1))
                  (kernelSuccessorNormalize pred mu c).2) := by
            change rawKernelSuccessorNormalize eta.1 mu.1 c=_
            rw [normalize_raw_def hf]
            simp only [hgt,ne_self_iff_false,if_false]
            rfl
          rw [heq]
          refine ⟨by simp,?_,?_⟩
          · intro p hm
            simp only [List.mem_cons] at hm
            rcases hm with rfl | hm
            · exact ⟨eta.2,hle,le_rfl⟩
            · have hh := hi.2.1 p hm
              exact ⟨hh.1,hh.2.1,hh.2.2.trans (show pred.1.repr≤eta.1.repr from hsmall.le)⟩
          · obtain ⟨pre,last,hw,hlast⟩ := hi.2.2
            refine ⟨(eta.1,c+(1+Vendor.R1.treeWeight pred.1))::pre,last,?_,hlast⟩
            simp only [hw,List.cons_append]
      | inr f =>
        rw [hf] at hprop
        have heq : kernelSuccessorNormalize eta mu c=([(eta.1,c)],c+1+Vendor.R1.treeWeight eta.1) := by
          change rawKernelSuccessorNormalize eta.1 mu.1 c=_
          rw [normalize_raw_def hf]
          simp only [hgt,ne_self_iff_false,if_false]
        rw [heq]
        refine ⟨by simp,?_,[],eta.1,by simp,Or.inr hprop.1⟩
        intro p hm
        simp only [List.mem_singleton] at hm
        subst p
        exact ⟨eta.2,hle,le_rfl⟩

private theorem normalize_base_action (eta : NONote) (c t : Nat)
    (ht : c+1+Vendor.R1.treeWeight eta.1≤t) :
    c+actualOrdinalNorm (Ordinal.omega0^eta.1.repr)≤t ∧
    actualPrincipalWordGenuine [(eta.1,c)] t ∧
    actualPrincipalWordRun [(eta.1,c)] t=
      (actualSuffixKernel (Ordinal.omega0^eta.1.repr) c t,
        actualSuffixKernelCount (Ordinal.omega0^eta.1.repr) c t) := by
  have hd : c+actualOrdinalNorm (Ordinal.omega0^eta.1.repr)≤t := by rw [normalize_power_norm]; omega
  exact ⟨hd,⟨hd,True.intro⟩,by simp [actualPrincipalWordRun]⟩

theorem actualKernelSuccessorNormalizeAction : Targets.ActualKernelSuccessorNormalizeAction := by
  intro eta
  induction eta using NONote.lt_wf.induction with
  | h eta ih =>
    intro mu hp hle c t ht
    by_cases hstop : ONote.cmp eta.1 mu.1 ≠ Ordering.gt
    · rw [normalize_stop eta mu c hstop] at ht ⊢
      exact normalize_base_action eta c t ht
    · have hgt : ONote.cmp eta.1 mu.1=Ordering.gt := by tauto
      have hlt := normalize_cmp_gt eta mu hgt
      have hprop := ONote.fundamentalSequence_has_prop eta.1
      cases hf : ONote.fundamentalSequence eta.1 with
      | inl x =>
        cases x with
        | none =>
          rw [hf] at hprop
          have hz : eta.1=0 := hprop
          have hzero : eta.1.repr=0 := by rw [hz]; rfl
          rw [hzero] at hlt
          exact (not_lt_of_ge hp.le hlt).elim
        | some a =>
          rw [hf] at hprop
          let pred : NONote := ⟨a,hprop.2 eta.2⟩
          have hsmall : pred<eta := by change a.repr<eta.1.repr; rw [hprop.1]; exact Order.lt_succ _
          have hchild : mu.1.repr≤pred.1.repr := by rw [hprop.1] at hlt; exact Order.lt_succ_iff.mp hlt
          have heq : kernelSuccessorNormalize eta mu c=
              ((eta.1,c+(1+Vendor.R1.treeWeight pred.1))::(kernelSuccessorNormalize pred mu c).1,
                max (c+(1+Vendor.R1.treeWeight pred.1)+(1+Vendor.R1.treeWeight eta.1))
                  (kernelSuccessorNormalize pred mu c).2) := by
            change rawKernelSuccessorNormalize eta.1 mu.1 c=_
            rw [normalize_raw_def hf]
            simp only [hgt,ne_self_iff_false,if_false]
            rfl
          rw [heq] at ht ⊢
          let H := Ordinal.omega0^eta.1.repr
          let theta := Ordinal.omega0^pred.1.repr
          let w := actualOrdinalNorm theta
          let V := actualSuffixKernel H (c+w) t
          have hnorm : w=1+Vendor.R1.treeWeight pred.1 := normalize_power_norm pred
          have hcommon : c+w+actualOrdinalNorm H≤t := by
            rw [hnorm,normalize_power_norm eta]
            exact (Nat.le_max_left _ _).trans ht
          have hV : t≤V := by
            have hh := iterate_index_mono (fun n => (self_lt_Phi n).le) t
              (Nat.zero_le (actualSuffixKernelCount H (c+w) t))
            exact hh
          have hchildT : (kernelSuccessorNormalize pred mu c).2≤V :=
            ((Nat.le_max_right _ _).trans ht).trans hV
          have hi := ih pred hsmall mu hp hchild c V hchildT
          have hH : theta*Ordinal.omega0=H := by
            dsimp [theta,H]
            rw [hprop.1,Order.succ_eq_add_one,Ordinal.opow_add_one]
          have hHeps : theta*Ordinal.omega0<epsilonZero := by
            rw [hH]
            exact (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr (normalRepresentationSound eta)
          have hcomp := actualSuccessorKernelComposition pred.1.repr (hp.trans_le hchild) hHeps c t
          have hcount := actualSuccessorCountCocycle pred.1.repr (hp.trans_le hchild) hHeps c t
          dsimp only at hcomp hcount
          rw [hH] at hcomp hcount
          have hvalue := hcomp hcommon
          have hnumber := hcount hcommon
          have hfirst : c+w+actualOrdinalNorm H≤t := hcommon
          refine ⟨?_,?_,?_⟩
          · change c+actualOrdinalNorm H≤t
            omega
          · change c+(1+Vendor.R1.treeWeight pred.1)+actualOrdinalNorm H≤t ∧ _
            rw [← hnorm]
            exact ⟨hfirst,hi.2.1⟩
          · change ( (actualPrincipalWordRun (kernelSuccessorNormalize pred mu c).1
                (actualSuffixKernel H (c+(1+Vendor.R1.treeWeight pred.1)) t)).1,
              actualSuffixKernelCount H (c+(1+Vendor.R1.treeWeight pred.1)) t+
                (actualPrincipalWordRun (kernelSuccessorNormalize pred mu c).1
                  (actualSuffixKernel H (c+(1+Vendor.R1.treeWeight pred.1)) t)).2) = _
            rw [← hnorm,hi.2.2]
            exact Prod.ext hvalue.symm hnumber.symm
      | inr f =>
        have heq : kernelSuccessorNormalize eta mu c=([(eta.1,c)],c+1+Vendor.R1.treeWeight eta.1) := by
          change rawKernelSuccessorNormalize eta.1 mu.1 c=_
          rw [normalize_raw_def hf]
          simp only [hgt,ne_self_iff_false,if_false]
        rw [heq] at ht ⊢
        exact normalize_base_action eta c t ht

end LogicLineages.OrdinalComparison
