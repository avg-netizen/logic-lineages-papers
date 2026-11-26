module
public import LogicLineages.PermittedControl.PureCertificateTargets
public import LogicLineages.PermittedControl.HighestPieceProof
public import LogicLineages.PermittedControl.ThickBlockFactsProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem numericalComparison_primrec : Primrec₂ numericalComparison :=
  (Primrec.ite Primrec.nat_lt (Primrec.const 0)
    (Primrec.ite Primrec.eq (Primrec.const 1) (Primrec.const 2))).to₂

 theorem profileCeilEffective : Primrec (fun n : Nat => (rawProfileCode n (rawNoteEncode (ONote.ofNat 1))+1)/2) := by
  have hp : Primrec (fun n : Nat => rawProfileCode n (rawNoteEncode (ONote.ofNat 1))) :=
    rawProfileEffective.comp Primrec.id (Primrec.const (rawNoteEncode (ONote.ofNat 1)))
  exact Primrec.nat_div.comp (Primrec.nat_add.comp hp (Primrec.const 1)) (Primrec.const 2)

 theorem profileSelectedSignEffective : Primrec₂ (fun p : Nat×Nat×Nat => fun n =>
    numericalComparison (rawProfileCode p.2.1 n) (rawProfileCode p.1 n)) := by
  have hm : Primrec (fun p : (Nat×Nat×Nat)×Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  have hn : Primrec (fun p : (Nat×Nat×Nat)×Nat => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  exact (numericalComparison_primrec.comp (rawProfileEffective.comp hn Primrec.snd)
    (rawProfileEffective.comp hm Primrec.snd)).to₂

 theorem profileSelectedBranchEffective : Primrec (fun p : Nat×Nat×Nat =>
    match highestPieceCode p.1 p.2.1 p.2.2 with
    | none => numericalComparison ((rawProfileCode p.2.1 (rawNoteEncode (ONote.ofNat 1))+1)/2)
        ((rawProfileCode p.1 (rawNoteEncode (ONote.ofNat 1))+1)/2)
    | some n => numericalComparison (rawProfileCode p.2.1 n) (rawProfileCode p.1 n)) := by
  have hm : Primrec (fun p : Nat×Nat×Nat => p.1) := Primrec.fst
  have hn : Primrec (fun p : Nat×Nat×Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hnone := numericalComparison_primrec.comp (profileCeilEffective.comp hn) (profileCeilEffective.comp hm)
  exact Primrec.option_casesOn highestPieceEffective hnone profileSelectedSignEffective

 theorem pureCertificateSignEffective : Primrec (fun p : Nat×Nat×Nat => pureCertificateCode p.1 p.2.1 p.2.2) := by
  have he : Primrec (fun p : Nat×Nat×Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have hguard : PrimrecPred (fun p : Nat×Nat×Nat => rawComparisonCode p.2.2 (rawNoteEncode (ONote.ofNat 1))=1) :=
    Primrec.eq.comp (rawComparisonPrimitiveRecursive.comp he (Primrec.const (rawNoteEncode (ONote.ofNat 1)))) (Primrec.const 1)
  exact (Primrec.ite hguard (Primrec.const 1) profileSelectedBranchEffective).of_eq (by intro p; rfl)

 theorem pureCertificateTailEffective : Primrec (fun p : Nat×Nat×Nat×Nat => pureCertificateTailCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hm : Primrec (fun p : Nat×Nat×Nat×Nat => p.1) := Primrec.fst
  have hn : Primrec (fun p : Nat×Nat×Nat×Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have he : Primrec (fun p : Nat×Nat×Nat×Nat => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hb : Primrec (fun p : Nat×Nat×Nat×Nat => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hnorm : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  have hr := Primrec.nat_add.comp (Primrec.const 100) (Primrec.nat_mul.comp (Primrec.const 4)
    (Primrec.nat_add.comp (Primrec.nat_add.comp (hnorm.comp hm) (hnorm.comp hn)) (hnorm.comp he)))
  exact thickBlockTailEffective.comp hr hb


 theorem pureCertificateEffective : Targets.PureCertificateEffective := ⟨pureCertificateSignEffective,pureCertificateTailEffective⟩

 theorem numericalComparison_compare (a b c d : Nat) (h : compare a b=compare c d) :
    numericalComparison a b=numericalComparison c d := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have hcd : c<d := compare_lt_iff_lt.mp ((compare_lt_iff_lt.mpr hab).symm ▸ h.symm)
    simp [numericalComparison,hab,hcd]
  · subst b
    have hcd : c=d := compare_eq_iff_eq.mp (by simpa using h.symm)
    subst d
    simp [numericalComparison]
  · have hcd : d<c := compare_gt_iff_gt.mp ((compare_gt_iff_gt.mpr hab).symm ▸ h.symm)
    simp [numericalComparison,not_lt_of_ge hab.le,hab.ne',not_lt_of_ge hcd.le,hcd.ne']

end LogicLineages.PermittedControl
