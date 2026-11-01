module
public import LogicLineages.OrdinalComparison.AffineSignProgramTargets
public import LogicLineages.OrdinalComparison.AffineProfileCertificateProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.AffineSignProgram

private theorem slope_strict (a b c d x : Nat) (ha : a<c) (hb : b<x) : a*x+b<c*x+d := by
  have hm := Nat.mul_le_mul_right x (Nat.succ_le_of_lt ha)
  rw [Nat.succ_mul] at hm
  omega

theorem program : Targets.AffineSourceSignProgram := by
  have ha : Primrec (fun p : Nat × Nat × Nat × Nat => p.1) := Primrec.fst
  have hb : Primrec (fun p : Nat × Nat × Nat × Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun p : Nat × Nat × Nat × Nat => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hd : Primrec (fun p : Nat × Nat × Nat × Nat => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hsign := Primrec.ite (Primrec.nat_lt.comp ha hc) (Primrec.const 0)
    (Primrec.ite (Primrec.nat_lt.comp hc ha) (Primrec.const 2)
      (Primrec.ite (Primrec.nat_lt.comp hb hd) (Primrec.const 0)
        (Primrec.ite (Primrec.nat_lt.comp hd hb) (Primrec.const 2) (Primrec.const 1))))
  refine ⟨hsign.pair (Primrec.succ.comp (Primrec.nat_add.comp hb hd)),?_⟩
  intro a b c d
  refine ⟨?_,?_,?_⟩
  · unfold encodedAffineSourceSign
    split_ifs <;> omega
  · change 1≤b+d+1
    omega
  · intro x hx
    change b+d+1≤x at hx
    have hxb : b<x := by omega
    have hxd : d<x := by omega
    by_cases hac : a<c
    · have h := slope_strict a b c d x hac hxb
      simp [encodedAffineSourceSign,hac,h,ne_of_lt h,not_lt_of_ge h.le]
    · by_cases hca : c<a
      · have h := slope_strict c d a b x hca hxd
        simp [encodedAffineSourceSign,hac,hca,h,Ne.symm (ne_of_lt h),not_lt_of_ge h.le]
      · have heq : a=c := by omega
        subst c
        by_cases hbd : b<d
        · have h : a*x+b<a*x+d := Nat.add_lt_add_left hbd _
          simp [encodedAffineSourceSign,hbd,h,ne_of_lt hbd,not_lt_of_ge h.le]
        · by_cases hdb : d<b
          · have h : a*x+d<a*x+b := Nat.add_lt_add_left hdb _
            simp [encodedAffineSourceSign,hbd,hdb,h,Ne.symm (ne_of_lt hdb),not_lt_of_ge h.le]
          · have heq : b=d := by omega
            subst d
            simp [encodedAffineSourceSign]

theorem positive_source : Targets.ActualAffinePositiveSourceSigns := by
  intro a b c d
  have h := program.2 a b c d
  refine ⟨h.1,h.2.1,?_⟩
  intro x hx
  simpa only [(AffineProfileCertificate.affine_source.2 a b).2.2 x,
    (AffineProfileCertificate.affine_source.2 c d).2.2 x] using h.2.2 x hx

theorem collected_source : Targets.ActualAffineCollectedSourceSigns := by
  intro a b c d
  have h := program.2 a b c d
  refine ⟨h.1,h.2.1,?_⟩
  intro x hx
  simpa only [actualCollectedPositiveEval,actualCollectedTagsEval,Nat.add_zero,
    Nat.add_comm b (a*x),Nat.add_comm d (c*x)] using h.2.2 x hx

end LogicLineages.OrdinalComparison.AffineSignProgram
