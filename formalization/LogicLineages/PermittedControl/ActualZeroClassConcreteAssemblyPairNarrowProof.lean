module
public import LogicLineages.PermittedControl.ConcreteCountPairReplacementTargets
import LogicLineages.PermittedControl.CountTransferCoreProof
import LogicLineages.PermittedControl.EntryTableProof
import LogicLineages.PermittedControl.InverseTableProof
import LogicLineages.PermittedControl.GapInputProof
import LogicLineages.PermittedControl.GapInputFoundationProof
import LogicLineages.PermittedControl.ThresholdUnequalProof
import LogicLineages.PermittedControl.ThresholdTailBridgeProof
import LogicLineages.PermittedControl.EntryLinearProof
import LogicLineages.PermittedControl.ClosedOrdinaryFieldActualProof
import LogicLineages.PermittedControl.FunnelProof
import LogicLineages.OrdinalComparison.OrdinalRepresentationSound

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassConcreteAssembly
open OrdinalComparison PreparedProjection FieldComparison ConcreteCountPairReplacement

/-! Use only the actual distinct-input and rank-transfer clauses of the
existing CountTransfer proof. Its finite zero-class polynomial identity
and associated tactic are irrelevant to this pair instantiation. -/

private theorem assemblyTransferSignCases (s : Nat) (h : s ≤ 2) : s = 0 ∨ s = 1 ∨ s = 2 := by omega

private theorem assemblyTransferTailParts (G T U C y : Nat) (h : 1+max G (max T (max U C)) ≤ y) :
    G ≤ y ∧ T ≤ y := by omega

private theorem assemblyTransferGuardParts (a k m y : Nat) (h : max 2 (max a (max k m)) ≤ y) :
    max 2 (max k m) ≤ y := by omega

private theorem assemblyDistinctInputGap : Targets.DistinctInputGap := by
  intro f B hf lam mu lam' mu' hlam hlam' hll hll' hmu hmu' hml hml' x y hx hy hxy i j hi hj heq
  by_contra hnot
  have hle : lam'-mu' ≤ lam-mu := not_lt.mp hnot
  obtain ⟨i0,j0,hi0,hj0,-,hlt⟩ :=
    (gapInputComparison f B hf lam mu lam' mu' hlam hlam' hll hll' hmu hmu' hml hml').2.1 hle
      y x hy hx hxy
  have ei := firstEntry_unique f _ _ i0 i hi0 hi
  have ej := firstEntry_unique f _ _ j0 j hj0 hj
  rw [ei,ej] at hlt
  exact absurd heq (Nat.ne_of_gt hlt)

private theorem assemblyRankTransfer : Targets.RankTransfer := by
  intro f B hf lambda mu nu delta hll hm hn hd hml hgap x y hx hy p q hp hq heq
  obtain ⟨hmk,hklam,i,j,p',q',lo,mid,hi',hi,hxh,hh,hj,hp',hq',hpij,hcont,-,-,-,-,-,-,hrows,-⟩ :=
    actualInverseTable f B hf lambda mu nu delta hll hm hn hd hml hgap x y hx hy
  have ep := firstEntry_unique f _ _ p' p hp' hp
  have eq' := firstEntry_unique f _ _ q' q hq' hq
  rw [ep] at hpij hcont hrows
  rw [eq'] at hrows
  -- equal values force the equality certificate and `y = E_H(x)`
  have hy_eq : y = entryNormAt f (countInitial lambda.1.repr x) i := by
    rcases assemblyTransferSignCases _ (equalGapCertificateEffective.2.2 (rawNoteEncode mu.1)
      (rawNoteEncode nu.1) (rawNoteEncode delta.1)) with h0 | h1 | h2
    · exact absurd heq (hrows.2.2 h0).2.1
    · exact ((hrows.1 h1).2.1).mp heq
    · exact absurd heq (hrows.2.1 h2).2.1
  rw [← hy_eq] at hj hcont
  -- both remaining entries start at `y`; their norms are iterates of `f` at `y`
  have hmu := normalRepresentationSound mu
  have hnu := normalRepresentationSound nu
  have hdelta := normalRepresentationSound delta
  have hk : mu.1.repr+delta.1.repr < epsilonZero := epsilonZero_add_principal hmu hdelta
  have hQ : nu.1.repr+delta.1.repr < epsilonZero := epsilonZero_add_principal hnu hdelta
  have hkl : Order.IsSuccLimit (mu.1.repr+delta.1.repr) := Ordinal.isSuccLimit_add _ hd
  have hql : Order.IsSuccLimit (nu.1.repr+delta.1.repr) := Ordinal.isSuccLimit_add _ hd
  have hnq : nu.1.repr < nu.1.repr+delta.1.repr := by
    simpa only [add_zero] using (add_lt_add_iff_left nu.1.repr).mpr hd.pos
  dsimp only [inverseTableTail] at hy
  have hparts := assemblyTransferTailParts _ _ _ _ y hy
  have hQtail := (gap_tail_bounds (mu.1.repr+delta.1.repr) mu.1.repr (nu.1.repr+delta.1.repr)
    nu.1.repr 0).2.1
  obtain ⟨j0,hj0,hjn⟩ := entryExistenceOrbit f B hf (mu.1.repr+delta.1.repr) mu.1.repr y hk hkl hm
    hmk (assemblyTransferGuardParts _ _ _ y hparts.1)
  obtain ⟨q0,hq0,hqn⟩ := entryExistenceOrbit f B hf (nu.1.repr+delta.1.repr) nu.1.repr y hQ hql hn
    hnq (hQtail.trans hparts.2)
  have ej := firstEntry_unique f _ _ j0 j hj0 hj
  have eq2 := firstEntry_unique f _ _ q0 q hq0 hq
  rw [ej] at hjn
  rw [eq2] at hqn
  have hjq : f^[j] y = f^[q] y := by
    rw [← hjn,← hqn,← hcont,heq]
  have ejq : j = q := (selected_iterate_strict f B hf y).injective hjq
  exact ⟨i,hi,hy_eq.symm,by rw [hpij,ejq]⟩

private theorem assemblySafeTailActual (lp mp lq mq : NONote) (B : Nat) :
    safeTailCode (intervalPairCodes lp mp lq mq) B =
      max (inverseTableTail lq mq mp (lp-mp) B)
        (gapInputTail lp.1.repr mp.1.repr lq.1.repr mq.1.repr 0) := by
  simp only [safeTailCode,intervalPairCodes]
  rw [ordinal_sub_note_code,inverseTableTailCode_correct,normal_encoded_gap_tail]

theorem assemblyActualPairReplacement : ActualPairReplacement := by
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
  rw [assemblySafeTailActual] at hx hy
  have hix : inverseTableTail lq mq mp delta B ≤ x := (le_max_left _ _).trans hx
  have hiy : inverseTableTail lq mq mp delta B ≤ y := (le_max_left _ _).trans hy
  have hgx : gapInputTail lp.1.repr mp.1.repr lq.1.repr mq.1.repr 0 ≤ x :=
    (le_max_right _ _).trans hx
  have hgy : gapInputTail lp.1.repr mp.1.repr lq.1.repr mq.1.repr 0 ≤ y :=
    (le_max_right _ _).trans hy
  have hgap : delta.1.repr < (lq-mq).1.repr := by
    simpa only [delta,note_sub_repr] using
      (assemblyDistinctInputGap f B hf lp.1.repr mp.1.repr lq.1.repr mq.1.repr
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
    assemblyRankTransfer f B hf lq mq mp delta hq.1 hq.2.1 hp.2.1 hdelta hq.2.2 hgap'
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

end LogicLineages.PermittedControl.ActualZeroClassConcreteAssembly
