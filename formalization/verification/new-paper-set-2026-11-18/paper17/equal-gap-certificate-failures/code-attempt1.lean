module
public import LogicLineages.PermittedControl.EqualGapCertificateTargets
public import LogicLineages.PermittedControl.InitialCodeProof
public import LogicLineages.PermittedControl.PureCertificateProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem numericalComparison_range (a b : Nat) : numericalComparison a b ≤ 2 := by
  unfold numericalComparison
  split
  · omega
  · split <;> omega

 theorem pureCertificateCode_range (mu nu E : Nat) : pureCertificateCode mu nu E ≤ 2 := by
  unfold pureCertificateCode
  split
  · omega
  · cases highestPieceCode mu nu E with
    | none => exact numericalComparison_range _ _
    | some n => exact numericalComparison_range _ _

 theorem equalGapCertificateSignEffective : Primrec (fun p : Nat×Nat×Nat => equalGapCertificateCode p.1 p.2.1 p.2.2) := by
  have hm : Primrec (fun p : Nat×Nat×Nat => p.1) := Primrec.fst
  have hn : Primrec (fun p : Nat×Nat×Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hd : Primrec (fun p : Nat×Nat×Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have he := originalLeadingCodeEffective.comp hd
  have hpass := (Primrec.eq.comp initialPassCodeEffective (Primrec.const true))
  have hyes := pureCertificateSignEffective.comp (hm.pair (hn.pair he))
  have hno := numericalComparison_primrec.comp (rawProfileEffective.comp hn he) (rawProfileEffective.comp hm he)
  exact (Primrec.ite hpass hyes hno).of_eq (by intro p; rfl)

 theorem equalGapCertificateTailEffective : Primrec (fun p : Nat×Nat×Nat×Nat => equalGapCertificateTailCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hm : Primrec (fun p : Nat×Nat×Nat×Nat => p.1) := Primrec.fst
  have hn : Primrec (fun p : Nat×Nat×Nat×Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hd : Primrec (fun p : Nat×Nat×Nat×Nat => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hb : Primrec (fun p : Nat×Nat×Nat×Nat => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hnorm : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  have hr := Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.const 20) (hnorm.comp hd)) (hnorm.comp hm)) (hnorm.comp hn)
  have he := originalLeadingCodeEffective.comp hd
  exact Primrec.nat_max.comp (thickBlockTailEffective.comp hr hb)
    (pureCertificateTailEffective.comp (hm.pair (hn.pair (he.pair hb))))

 theorem equalGapCertificateEffective : Targets.EqualGapCertificateEffective := by
  refine ⟨equalGapCertificateSignEffective,equalGapCertificateTailEffective,?_⟩
  intro mu nu delta
  unfold equalGapCertificateCode
  split
  · exact pureCertificateCode_range _ _ _
  · exact numericalComparison_range _ _

 theorem equalGap_tail_initial (mu nu delta : NONote) (B t : Nat)
    (ht : equalGapCertificateTailCode (rawNoteEncode mu.1) (rawNoteEncode nu.1) (rawNoteEncode delta.1) B ≤ t) :
    thickBlockTail (initialPeelingRadius mu.1.repr nu.1.repr delta.1.repr) B ≤ t := by
  have h := (le_max_left _ _).trans ht
  have hm := (rawNormCodeCorrect mu.1).trans (actualOrdinalNorm_notationCorrespondence mu).symm
  have hn := (rawNormCodeCorrect nu.1).trans (actualOrdinalNorm_notationCorrespondence nu).symm
  have hd := (rawNormCodeCorrect delta.1).trans (actualOrdinalNorm_notationCorrespondence delta).symm
  simpa only [hm,hn,hd,initialPeelingRadius] using h

 theorem numericalComparison_zero (a b : Nat) : numericalComparison a b=0 ↔ a<b := by
  simp only [numericalComparison]
  split
  · omega
  · split <;> omega
 theorem numericalComparison_one (a b : Nat) : numericalComparison a b=1 ↔ a=b := by
  simp only [numericalComparison]
  split
  · omega
  · split <;> omega
 theorem numericalComparison_two (a b : Nat) : numericalComparison a b=2 ↔ b<a := by
  simp only [numericalComparison]
  split
  · omega
  · split <;> omega

end LogicLineages.PermittedControl
