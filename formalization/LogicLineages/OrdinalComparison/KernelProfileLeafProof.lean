module
public import LogicLineages.OrdinalComparison.KernelProfileLeafTargets
public import LogicLineages.OrdinalComparison.AffineProfileCertificateProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelProfileLeaf

theorem source_growth : Targets.ActualOpenComparisonSourceGrowth := by
  intro A hv hopen x hx
  cases A with
  | positive E => exact ⟨True.intro,OneVariableComparison.open_lower E hv hopen x⟩
  | range w E =>
    have hop := OneVariableComparison.open_lower E hv.2.2.1 hv.2.2.2 x
    have hdom := OneVariableComparison.word_domains w _ (hx.trans hop)
    exact ⟨hdom.1,hop.trans hdom.2⟩

theorem bounded_program : Targets.ActualBoundedKernelProfileLeafProgram := by
  have hL : Primrec (fun p : Nat × Nat × Nat => p.1) := Primrec.fst
  have hP : Primrec (fun p : Nat × Nat × Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun p : Nat × Nat × Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  refine ⟨Primrec.nat_max.comp (ProfileThresholdProgram.supplier_program.1.comp hL hP)
    (Primrec.nat_add.comp hc ((Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive).comp hL)),?_⟩
  intro L hprincipal hlarge P hP c t ht
  have hsup : encodedProfileSupplierTail (rawNoteEncode L.1) (positiveExprEncode P)≤t :=
    (Nat.le_max_left _ _).trans ht
  have hnorm : rawNormCode (rawNoteEncode L.1)=actualOrdinalNorm L.1.repr :=
    (rawNormCodeCorrect L.1).trans (actualOrdinalNorm_notationCorrespondence L).symm
  have hdom : c+actualOrdinalNorm L.1.repr≤t := by
    rw [← hnorm]
    exact (Nat.le_max_right _ _).trans ht
  have hT := (ProfileThresholdProgram.supplier_program.2 L P).1
  have hg := actualUniformProfileDirectGrowth L hprincipal hlarge P hP t c (hT.trans hsup) hdom
  exact ⟨hdom,fun s hs => (actualFixedLimitProfileMonotone L.1.repr P hP hs).trans_lt hg⟩

theorem affine_inputs_program : Targets.ActualAffineKernelIntegerInputsProgram := by
  refine ⟨AffineProfileCertificate.actual_program.1,?_⟩
  intro L hprincipal hlarge P hP c a b x t hN hxt
  let A : FixedLimitPositiveExpr := .add .input (.constant (t-x))
  have hv : fixedLimitProfileBelow epsilonZero A := ⟨True.intro,True.intro⟩
  have hop : positiveExprHasInput A=true := rfl
  have h := AffineProfileCertificate.actual_program.2 L hprincipal hlarge P A hP hv hop c a b x hN
  have hvalue : actualFixedLimitProfileEval A x=t := by
    change x+(t-x)=t
    omega
  simpa only [hvalue] using h

end LogicLineages.OrdinalComparison.KernelProfileLeaf
