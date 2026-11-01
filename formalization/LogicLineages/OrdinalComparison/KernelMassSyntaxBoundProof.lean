module
public import LogicLineages.OrdinalComparison.KernelMassProgramTargets
public import LogicLineages.OrdinalComparison.FiniteTail
public import LogicLineages.OrdinalComparison.ActualOrdinalNorm

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelMassProgram

private theorem threshold_equation {o : ONote} {x} (e : ONote.fundamentalSequence o=x) :
    rawStrictMassThreshold o =
      match (motive := (x : Option ONote ⊕ (Nat → ONote)) → ONote.FundamentalSequenceProp o x → Nat)
        x, e ▸ ONote.fundamentalSequence_has_prop o with
      | Sum.inl none, _ => 0
      | Sum.inl (some a), _ =>
        max 4 (max (1+Vendor.R1.treeWeight o)
          (max (2*(1+Vendor.R1.treeWeight a))
            (max (max 8 (1+Vendor.R1.treeWeight a))
              (if a=ONote.ofNat 2 then 0 else rawStrictMassThreshold a))))
      | Sum.inr _, _ => max 7 (2+Vendor.R1.treeWeight o) := by
  subst x
  rw [rawStrictMassThreshold]
  rfl

private theorem successor_weight (eta pred : NONote)
    (h : eta.1.repr=pred.1.repr+1) :
    Vendor.R1.treeWeight eta.1=Vendor.R1.treeWeight pred.1+1 := by
  have hf := finiteTailCorrect pred 1
  have hn : actualOrdinalNorm eta.1.repr=Vendor.R1.treeWeight pred.1+1 := by
    calc
      actualOrdinalNorm eta.1.repr=actualOrdinalNorm (finiteTail pred 1).1.repr := by
        apply congrArg actualOrdinalNorm
        rw [hf.1]
        simpa only [Nat.cast_one] using h
      _ = Vendor.R1.treeWeight (finiteTail pred 1).1 := actualOrdinalNorm_notationCorrespondence _
      _ = Vendor.R1.treeWeight pred.1+1 := hf.2
  exact (actualOrdinalNorm_notationCorrespondence eta).symm.trans hn

theorem strict_mass_bound : Targets.ActualStrictMassSyntaxBound := by
  intro eta
  induction eta using NONote.lt_wf.induction with
  | h eta ih =>
    have hp := ONote.fundamentalSequence_has_prop eta.1
    cases hf : ONote.fundamentalSequence eta.1 with
    | inl x =>
      cases x with
      | none =>
        change rawStrictMassThreshold eta.1≤_
        rw [threshold_equation hf]
        change 0≤10+2*Vendor.R1.treeWeight eta.1
        omega
      | some a =>
        rw [hf] at hp
        let pred : NONote := ⟨a,hp.2 eta.2⟩
        have hrepr : eta.1.repr=pred.1.repr+1 := by
          simpa only [Order.succ_eq_add_one] using hp.1
        have hsmall : pred<eta := by
          change pred.1.repr<eta.1.repr
          rw [hrepr]
          exact Order.lt_add_one_iff.mpr le_rfl
        have hweight := successor_weight eta pred hrepr
        have hi := ih pred hsmall
        change rawStrictMassThreshold a≤10+2*Vendor.R1.treeWeight a at hi
        change Vendor.R1.treeWeight eta.1=Vendor.R1.treeWeight a+1 at hweight
        change rawStrictMassThreshold eta.1≤_
        rw [threshold_equation hf]
        by_cases hb : a=ONote.ofNat 2
        · simp only [if_pos hb]
          omega
        · simp only [if_neg hb]
          omega
    | inr f =>
      change rawStrictMassThreshold eta.1≤_
      rw [threshold_equation hf]
      change max 7 (2+Vendor.R1.treeWeight eta.1)≤10+2*Vendor.R1.treeWeight eta.1
      omega

end LogicLineages.OrdinalComparison.KernelMassProgram
