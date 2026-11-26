module
public import LogicLineages.PermittedControl.ConcreteCountPairReplacementTargets
import LogicLineages.PermittedControl.ThresholdUnequalProof
import LogicLineages.PermittedControl.ThresholdNumericProgramsProof
import LogicLineages.PermittedControl.CountTransferProof
import LogicLineages.PermittedControl.EntryLinearProof
import LogicLineages.PermittedControl.ClosedOrdinaryFieldActualProof
import LogicLineages.PermittedControl.FunnelProof
import LogicLineages.PermittedControl.OrdinalEndpointCodeProof
import LogicLineages.OrdinalComparison.OrdinalRepresentationSound

@[expose] public section
namespace LogicLineages.PermittedControl.ConcreteCountPairReplacement
open OrdinalComparison PreparedProjection FieldComparison

private theorem replacementPrimitive : Primrec₂ replacementCode := by
  let A := Nat × IntervalPairCodes
  have hp : Primrec (fun z : A => z.2.1) := Primrec.fst.comp Primrec.snd
  have hq : Primrec (fun z : A => z.2.2) := Primrec.snd.comp Primrec.snd
  have hd := ordinalSubCodeEffective.comp (Primrec.fst.comp hp) (Primrec.snd.comp hp)
  have hk := ordinalAddCodeEffective.comp (Primrec.snd.comp hq) hd
  exact (Primrec.const 2).pair (Primrec.fst.pair
    ((Primrec.const 1).pair ((Primrec.const 0).pair ((Primrec.fst.comp hq).pair hk))))

private theorem safeTailPrimitive : Primrec₂ safeTailCode := by
  let A := IntervalPairCodes × Nat
  have hp : Primrec (fun z : A => z.1.1) := Primrec.fst.comp Primrec.fst
  have hq : Primrec (fun z : A => z.1.2) := Primrec.snd.comp Primrec.fst
  have hlp := Primrec.fst.comp hp
  have hmp := Primrec.snd.comp hp
  have hlq := Primrec.fst.comp hq
  have hmq := Primrec.snd.comp hq
  have hi := inverseTableTailCode_primrec hlq hmq hmp
    (ordinalSubCodeEffective.comp hlp hmp) Primrec.snd
  have hn : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  have hg : Primrec (fun z : A =>
      encodedGapInputTail (z.1.1.1,z.1.1.2,z.1.2.1,z.1.2.2,0)) := by
    simpa only [encodedGapInputTail,Nat.mul_zero,Nat.add_zero] using
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp
          (Primrec.nat_add.comp (Primrec.const 2) (hn.comp hlp))
          (hn.comp hlq))
        (Primrec.nat_max.comp (Primrec.const 1)
          (Primrec.nat_max.comp (hn.comp hmp) (hn.comp hmq))))
  exact Primrec.nat_max.comp hi hg

private theorem replacementLiteral (r0 : Nat) (lp mp lq mq : NONote) :
    replacementCode r0 (intervalPairCodes lp mp lq mq) =
      (replacementOperand r0 lp mp lq mq).code := by
  simp only [replacementCode,intervalPairCodes,replacementOperand,LowerOperand.code,longFieldCode]
  rw [ordinal_sub_note_code,ordinal_add_note_code]

private theorem safeTailActual (lp mp lq mq : NONote) (B : Nat) :
    safeTailCode (intervalPairCodes lp mp lq mq) B =
      max (inverseTableTail lq mq mp (lp-mp) B)
        (gapInputTail lp.1.repr mp.1.repr lq.1.repr mq.1.repr 0) := by
  simp only [safeTailCode,intervalPairCodes]
  rw [ordinal_sub_note_code,inverseTableTailCode_correct,normal_encoded_gap_tail]

theorem codeExact : CodeExact :=
  ⟨replacementPrimitive,safeTailPrimitive,replacementLiteral,safeTailActual⟩

theorem actualPairReplacement : ActualPairReplacement := by
  intro f B hf lp mp lq mq hp hq ρ r0 r1 p q
  dsimp only
  intro hx hy hxy hQ hP hfull
  let x := ρ r0
  let y := ρ r1
  let delta := lp-mp
  let kappa := mq+delta
  have hcore : entryNormAt f (countInitial lp.1.repr y) q =
      entryNormAt f (countInitial lq.1.repr x) p :=
    (selected_threshold_admissible f B hf).1.injective hfull
  rw [safeTailActual] at hx hy
  have hix : inverseTableTail lq mq mp delta B ≤ x := (le_max_left _ _).trans hx
  have hiy : inverseTableTail lq mq mp delta B ≤ y := (le_max_left _ _).trans hy
  have hgx : gapInputTail lp.1.repr mp.1.repr lq.1.repr mq.1.repr 0 ≤ x :=
    (le_max_right _ _).trans hx
  have hgy : gapInputTail lp.1.repr mp.1.repr lq.1.repr mq.1.repr 0 ≤ y :=
    (le_max_right _ _).trans hy
  have hgap : delta.1.repr < (lq-mq).1.repr := by
    simpa only [delta,note_sub_repr] using
      (distinctInputGap f B hf lp.1.repr mp.1.repr lq.1.repr mq.1.repr
        (rawNotation_repr_lt_epsilonZero lp.1) (rawNotation_repr_lt_epsilonZero lq.1)
        hp.1 hq.1 hp.2.1 hq.2.1 hp.2.2 hq.2.2 x y hgx hgy hxy q p hP hQ hcore)
  obtain ⟨hdelta,hPadd⟩ := proper_gap_note lp mp hp
  obtain ⟨hk_lt,hm_lt,j,h,_,hj,hj_norm,hj_mem,_⟩ :=
    threshold_unequal_table f B hf lq mq lp mp hq hp x y p q hix hiy hgap hQ hP
  have hP' : FirstEntry f (countInitial (mp.1.repr+delta.1.repr) y) mp.1.repr q := by
    rw [hPadd]
    exact hP
  have hcore' : entryNormAt f (countInitial (mp.1.repr+delta.1.repr) y) q =
      entryNormAt f (countInitial lq.1.repr x) p := by
    rw [hPadd]
    exact hcore
  have hgap' : delta.1.repr < lq.1.repr-mq.1.repr := by
    simpa only [note_sub_repr] using hgap
  obtain ⟨i,hi,hi_norm,hcount⟩ :=
    rankTransfer f B hf lq mq mp delta hq.1 hq.2.1 hp.2.1 hdelta hq.2.2 hgap'
      x y hix hiy p q hQ hP' hcore'
  have hji : j=i := firstEntry_unique f _ _ j i hj hi
  rw [hji,hi_norm] at hj_norm
  rw [hji,hj_norm] at hj_mem
  have hkap : kappa.1.repr = mq.1.repr+delta.1.repr := note_add_repr mq delta
  have hkl : kappa.1.repr < lq.1.repr := by rw [hkap]; exact hk_lt
  have hmk : mq.1.repr < kappa.1.repr := by rw [hkap]; exact hm_lt
  have hlim : Order.IsSuccLimit kappa.1.repr := by
    rw [hkap]
    exact Ordinal.isSuccLimit_add _ hdelta
  have hproper : Targets.ProperIntervalNotes lq kappa :=
    ⟨hq.1,Or.inr hlim,hkl⟩
  have haff : actualOrdinalNorm lq.1.repr ≤ x := by
    have hix' := hix
    dsimp only [inverseTableTail] at hix'
    have ht := threshold_guard_arithmetic _ _ _ _ _ hix'
    exact (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have hdom : ClosedOrdinaryValueDomain (.entry 0 lq kappa) x :=
    ⟨hproper,haff⟩
  have hi' : FirstEntry f (countInitial lq.1.repr x) kappa.1.repr i := by
    rw [hkap]
    exact hi
  have hread : closedOrdinaryCountField f (rawNoteEncode lq.1,
      ordinalAddCode (rawNoteEncode mq.1) (rawNoteEncode delta.1),x) = some (some i) := by
    rw [ordinal_add_note_code]
    exact (((closedOrdinaryCountActual f lq kappa x).2 hdom).1 i).mpr hi'
  exact ⟨hgap,hmk,hkl,hproper,rfl,
    i,hi',hi_norm,hj_mem,hcount,by omega,hdom,⟨hdom,hi'⟩,hread⟩

theorem fullConcretePairReplacement : FullConcretePairReplacement :=
  ⟨codeExact,actualPairReplacement⟩

end LogicLineages.PermittedControl.ConcreteCountPairReplacement
