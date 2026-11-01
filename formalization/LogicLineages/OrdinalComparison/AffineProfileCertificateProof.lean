module
public import LogicLineages.OrdinalComparison.AffineProfileCertificateTargets
public import LogicLineages.OrdinalComparison.ProfileCompositionProof
public import LogicLineages.OrdinalComparison.ProfileThresholdProgramProof
public import LogicLineages.OrdinalComparison.MultivariatePositiveRayProof
public import LogicLineages.OrdinalComparison.OneVariableComparisonDomainsProof
public import LogicLineages.OrdinalComparison.ProfileDirectProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.AffineProfileCertificate

private theorem multiple_below (L : Ordinal.{0}) (a : Nat) :
    fixedLimitProfileBelow L (positiveInputMultiple a) := by
  induction a with
  | zero => trivial
  | succ a ih => exact ⟨ih,True.intro⟩

theorem affine_source : Targets.ActualAffineProfileSource := by
  have ha : Primrec (fun p : Nat × Nat => positiveInputMultipleCode p.1) :=
    MultivariatePositiveRay.code.1.comp Primrec.fst
  have hb := Primrec.nat_mul.comp (Primrec.const 4) (Primrec.snd : Primrec (fun p : Nat × Nat => p.2))
  refine ⟨Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4)
    (Primrec₂.natPair.comp ha hb)) (Primrec.const 2),?_⟩
  intro a b
  refine ⟨?_,fun L => ⟨multiple_below L a,True.intro⟩,?_⟩
  · unfold positiveAffineProfileCode positiveAffineProfile positiveExprEncode
    rw [MultivariatePositiveRay.source.1]
    rfl
  · intro x
    change actualFixedLimitProfileEval (positiveInputMultiple a) x+b=a*x+b
    rw [MultivariatePositiveRay.source.2.1]

theorem actual_program : Targets.ActualAffineProfileCertificateProgram := by
  have hL : Primrec (fun p : Nat × Nat × Nat × Nat × Nat => p.1) := Primrec.fst
  have hP : Primrec (fun p : Nat × Nat × Nat × Nat × Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun p : Nat × Nat × Nat × Nat × Nat => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ha : Primrec (fun p : Nat × Nat × Nat × Nat × Nat => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hb : Primrec (fun p : Nat × Nat × Nat × Nat × Nat => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have haf := affine_source.1.comp ha hb
  have hcomp := ProfileComposition.program.1.comp hP haf
  have hsup := ProfileThresholdProgram.supplier_program.1.comp hL hcomp
  have hnorm := (Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive).comp hL
  refine ⟨Primrec.nat_max.comp hsup (Primrec.nat_add.comp hc hnorm),?_⟩
  intro L hprincipal hlarge P A hP hA hopen c a b x hx
  have harg := OneVariableComparison.open_lower A hA hopen x
  have haf := affine_source.2 a b
  have hcomp := ProfileComposition.source L.1.repr P (positiveAffineProfile a b) hP (haf.2.1 _)
  have hsource : encodedProfileCompose (positiveExprEncode P) (positiveAffineProfileCode a b)=
      positiveExprEncode (fixedProfileCompose P (positiveAffineProfile a b)) := by
    rw [haf.1,ProfileComposition.program.2]
  have hsup : encodedProfileSupplierTail (rawNoteEncode L.1)
      (positiveExprEncode (fixedProfileCompose P (positiveAffineProfile a b)))≤x := by
    rw [← hsource]
    exact (Nat.le_max_left _ _).trans hx
  have hT := (ProfileThresholdProgram.supplier_program.2 L (fixedProfileCompose P (positiveAffineProfile a b))).1
  have hmass : c+actualOrdinalNorm L.1.repr≤x := by
    have hraw : rawNormCode (rawNoteEncode L.1)=actualOrdinalNorm L.1.repr :=
      (rawNormCodeCorrect L.1).trans (actualOrdinalNorm_notationCorrespondence L).symm
    rw [← hraw]
    exact (Nat.le_max_right _ _).trans hx
  have hbound := hmass.trans harg
  have hg := actualUniformProfileDirectGrowth L hprincipal hlarge
    (fixedProfileCompose P (positiveAffineProfile a b)) hcomp.1 _ c (hT.trans (hsup.trans harg)) hbound
  rw [hcomp.2,haf.2.2] at hg
  have hmono := actualFixedLimitProfileMonotone L.1.repr P hP
    (Nat.add_le_add_right (Nat.mul_le_mul_left a harg) b)
  exact ⟨hbound,hmono.trans_lt hg⟩

end LogicLineages.OrdinalComparison.AffineProfileCertificate
