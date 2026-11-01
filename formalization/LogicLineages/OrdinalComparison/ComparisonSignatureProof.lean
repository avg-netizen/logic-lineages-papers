module
public import LogicLineages.OrdinalComparison.ComparisonSignatureTargets
public import LogicLineages.OrdinalComparison.EncodedNormBallProof
public import LogicLineages.OrdinalComparison.RawComparisonProof
public import LogicLineages.OrdinalComparison.PrincipalBlocksProof
public import LogicLineages.OrdinalComparison.FiniteTail
public import LogicLineages.OrdinalComparison.ActualOrdinalNorm

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonSignature

private theorem filter_le (w : List Nat) (p q : Nat → Bool)
    (hsub : ∀ n∈w,p n=true → q n=true) : (w.filter p).length≤(w.filter q).length := by
  induction w with
  | nil => exact Nat.le_refl 0
  | cons a w ih =>
    have ht := ih (fun n hn => hsub n (List.mem_cons_of_mem a hn))
    have ha := hsub a (by simp)
    cases hp : p a <;> cases hq : q a <;> simp_all [List.filter_cons] <;> omega

private theorem filter_lt (w : List Nat) (p q : Nat → Bool)
    (hsub : ∀ n∈w,p n=true → q n=true)
    (hex : ∃ n∈w,p n=false ∧ q n=true) : (w.filter p).length<(w.filter q).length := by
  induction w with
  | nil => simpa using hex
  | cons a w ih =>
    have htail := fun n hn => hsub n (List.mem_cons_of_mem a hn)
    have ha := hsub a (by simp)
    rcases hex with ⟨n,hn,hp,hq⟩
    rcases List.mem_cons.mp hn with heq | hn
    · subst n
      have ht := filter_le w p q htail
      simp only [List.filter_cons,hp,hq,Bool.false_eq_true,↓reduceIte,List.length_cons]
      omega
    · have ht := ih htail ⟨n,hn,hp,hq⟩
      cases hp0 : p a <;> cases hq0 : q a <;> simp_all [List.filter_cons] <;> omega

private theorem actual_code_lt (budget n : Nat) (hn : n∈encodedNormalNormBall budget) (eta : NONote) :
    (rawComparisonCode n (rawNoteEncode eta.1)=0 ↔ (rawNoteDecode n).repr<eta.1.repr) := by
  have hNF := ((encodedNormalNormBallDecodeCorrect budget n).mp hn).1
  let nu : NONote := ⟨rawNoteDecode n,hNF⟩
  simpa only [nu,rawNoteEncodeDecode n] using (rawComparisonOrdinalCorrect nu eta).1

private theorem rank_primitive : Primrec₂ encodedComparisonSignatureRank := by
  have hp : PrimrecRel (fun n eta : Nat => rawComparisonCode n eta=0) :=
    Primrec.eq.comp rawComparisonPrimitiveRecursive (Primrec.const 0)
  exact Primrec.list_length.comp
    (hp.listFilter.comp (encodedNormalNormBallPrimitiveRecursive.comp Primrec.fst) Primrec.snd)

theorem rank_program : Targets.ComparisonSignatureRankProgram := by
  refine ⟨rank_primitive,?_,?_⟩
  · intro budget eta hbound
    have hmem : rawNoteEncode eta.1∈encodedNormalNormBall budget :=
      (encodedNormalNormBallCorrect budget eta.1).mpr ⟨eta.2,hbound⟩
    have hself : decide (rawComparisonCode (rawNoteEncode eta.1) (rawNoteEncode eta.1)=0)=false := by
      apply decide_eq_false_iff_not.mpr
      intro h
      exact (lt_irrefl eta.1.repr) ((rawComparisonOrdinalCorrect eta eta).1.mp h)
    have hh := filter_lt (encodedNormalNormBall budget)
      (fun n => decide (rawComparisonCode n (rawNoteEncode eta.1)=0)) (fun _ => true)
      (by intro _ _ _; rfl) ⟨rawNoteEncode eta.1,hmem,hself,rfl⟩
    simpa only [encodedComparisonSignatureRank,List.filter_true] using hh
  · intro budget eta zeta hEta _ hlt
    have hmem : rawNoteEncode eta.1∈encodedNormalNormBall budget :=
      (encodedNormalNormBallCorrect budget eta.1).mpr ⟨eta.2,hEta⟩
    have hself : decide (rawComparisonCode (rawNoteEncode eta.1) (rawNoteEncode eta.1)=0)=false := by
      apply decide_eq_false_iff_not.mpr
      intro h
      exact (lt_irrefl eta.1.repr) ((rawComparisonOrdinalCorrect eta eta).1.mp h)
    apply filter_lt (encodedNormalNormBall budget)
      (fun n => decide (rawComparisonCode n (rawNoteEncode eta.1)=0))
      (fun n => decide (rawComparisonCode n (rawNoteEncode zeta.1)=0))
    · intro n hn hp
      apply decide_eq_true_iff.mpr
      apply (actual_code_lt budget n hn zeta).mpr
      exact ((actual_code_lt budget n hn eta).mp (decide_eq_true_iff.mp hp)).trans hlt
    · exact ⟨rawNoteEncode eta.1,hmem,hself,
        decide_eq_true_iff.mpr ((rawComparisonOrdinalCorrect eta zeta).1.mpr hlt)⟩

private theorem block_weight (o eta : ONote) (hmem : eta∈principalExponentBlocks o) :
    Vendor.R1.treeWeight eta≤Vendor.R1.treeWeight o := by
  induction o with
  | zero => simp [principalExponentBlocks] at hmem
  | oadd e c t ihe iht =>
    simp only [principalExponentBlocks,List.mem_append] at hmem
    rcases hmem with hhead | htail
    · have heq := (List.mem_replicate.mp hhead).2
      subst eta
      rcases c with ⟨c,hc⟩
      change Vendor.R1.treeWeight e≤c*(1+Vendor.R1.treeWeight e)+Vendor.R1.treeWeight t
      have hm := Nat.mul_le_mul_right (1+Vendor.R1.treeWeight e) hc
      simp only [Nat.one_mul] at hm
      omega
    · have h := iht htail
      change Vendor.R1.treeWeight eta≤(c:Nat)*(1+Vendor.R1.treeWeight e)+Vendor.R1.treeWeight t
      omega

theorem principal_coverage : Targets.ComparisonSignaturePrincipalCoverage := by
  intro budget rho hbound eta hmem
  have hNF := (actualPrincipalBlocksNormalOrder rho.1 rho.2).1 eta hmem
  exact (encodedNormalNormBallCorrect budget eta).mpr
    ⟨hNF,(block_weight rho.1 eta hmem).trans hbound⟩

private theorem successor_weight (eta pred : NONote) (h : eta.1.repr=pred.1.repr+1) :
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

theorem successor_closure : Targets.ComparisonSignatureSuccessorClosure := by
  refine ⟨successor_weight,?_⟩
  intro budget eta pred hbound hs
  have h := successor_weight eta pred hs
  exact (encodedNormalNormBallCorrect budget pred.1).mpr ⟨pred.2,by omega⟩

end LogicLineages.OrdinalComparison.ComparisonSignature
