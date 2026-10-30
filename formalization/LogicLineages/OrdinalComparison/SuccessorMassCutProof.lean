module
public import LogicLineages.OrdinalComparison.SuccessorMassCutTargets
public import LogicLineages.OrdinalComparison.SuccessorMassResidualProof
public import LogicLineages.OrdinalComparison.CompensatedSyncProof
public import LogicLineages.OrdinalComparison.SuccessorKernelCutProof
public import LogicLineages.OrdinalComparison.ControlSegmentProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem successor_cut_nat_norm (n : Nat) : actualOrdinalNorm (n : Ordinal)=n := by
  have h := actualOrdinalNorm_notationCorrespondence (NONote.ofNat n)
  rw [norm_ofNat] at h
  change actualOrdinalNorm (ONote.ofNat n).repr=n at h
  simpa only [ONote.repr_ofNat] using h

theorem actualCompensatedPrincipalRetainedCut (gamma : Ordinal.{0}) (hg : 0 < gamma)
    (he : Ordinal.omega0^gamma < epsilonZero) (R c seed : Nat) (r : Ordinal.{0})
    (hr : r < epsilonZero) (hrbound : r < Ordinal.omega0^(gamma+1))
    (htotal : c+R*actualOrdinalNorm (Ordinal.omega0^gamma)+actualOrdinalNorm r=seed) :
    let pi := Ordinal.omega0^gamma
    let p := c+R*actualOrdinalNorm pi
    let q := actualControlledCount (compensatedPrefixControl p) r
    let V := (Phi^[q]) seed
    q ≤ actualControlledCount (compensatedPrefixControl c) (pi*(R : Ordinal)+r) ∧
    (∀ i, i ≤ q → actualControlledStateAfter (compensatedPrefixControl c) (pi*(R : Ordinal)+r) i =
      pi*(R : Ordinal)+actualControlledStateAfter (compensatedPrefixControl p) r i) ∧
    p ≤ V ∧ (V-p)+p=V ∧
    actualControlledStateAfter (compensatedPrefixControl c) (pi*(R : Ordinal)+r) q =
      pi*(R : Ordinal)+((V-p : Nat) : Ordinal) := by
  dsimp only
  let pi := Ordinal.omega0^gamma
  let pref := pi*(R : Ordinal)
  let p := c+R*actualOrdinalNorm pi
  let q := actualControlledCount (compensatedPrefixControl p) r
  let V := (Phi^[q]) seed
  have hpm := reserveStagePrincipalMultipleFacts gamma he R
  have hmin : actualMinExponentAtLeast pref gamma :=
    (actualMinExponentDivisibility pref hpm.1 gamma).mpr ⟨(R : Ordinal), rfl⟩
  have hbudget : ∀ n, actualOrdinalNorm pref ≤ compensatedPrefixControl c (actualOrdinalNorm pref+n) := by
    intro n
    exact (Nat.le_add_right _ _).trans ((compensatedPrefixControlBounds c).2 _).2.le
  have hctrl : prefixRemainderControl (compensatedPrefixControl c) (actualOrdinalNorm pref) =
      compensatedPrefixControl p := by
    rw [hpm.2, actualCompensatedControlComposition]
  have hcount := actualRetainedPrefixCountDecomposition (compensatedPrefixControl c) pref r
    hpm.1 hr gamma hg hmin hrbound hbudget
  have htrace := actualPrefixControlTrace (compensatedPrefixControl c) pref r
    hpm.1 hr gamma hg hmin hrbound hbudget
  dsimp only at hcount htrace
  rw [hctrl] at hcount htrace
  obtain ⟨m, hm, _⟩ := hcount.2.2
  have hn := actualControlledNormIteration (compensatedPrefixControl p) r hr q le_rfl
  have hiter := reserveCompensatedIteration p (actualOrdinalNorm r) q
  have hseed : p+actualOrdinalNorm r=seed := htotal
  rw [hseed] at hiter
  have hsum : p+actualOrdinalNorm (actualControlledStateAfter (compensatedPrefixControl p) r q)=V := by
    rw [hn]
    exact hiter
  have hmN : actualOrdinalNorm (actualControlledStateAfter (compensatedPrefixControl p) r q)=m := by
    rw [hm, successor_cut_nat_norm]
  have hpV : p ≤ V := by omega
  have hmeq : m=V-p := by omega
  refine ⟨hcount.1, htrace.1, hpV, Nat.sub_add_cancel hpV, ?_⟩
  rw [htrace.1 q le_rfl, hm, hmeq]

theorem actualSuccessorMassResidualCuts : Targets.ActualSuccessorMassResidualCuts := by
  intro gamma hg he B c e hce heB hbudget
  dsimp only
  let theta := Ordinal.omega0^gamma
  let L := theta*Ordinal.omega0
  let w := actualOrdinalNorm theta
  let q := (B-e)/w
  let qc := (B-c)/w
  let re := actualMaximumPredecessor theta ((B-e)%w)
  let rc := actualMaximumPredecessor theta ((B-c)%w)
  let rhi := theta*((qc-q : Nat) : Ordinal)+rc
  let Alo := actualMaximumPredecessor L (B-e)
  let Ahi := actualMaximumPredecessor L (B-c)
  let pe := e+q*w
  let pc := c+q*w
  let Ce := actualControlledCount (compensatedPrefixControl pe) re
  let Cc := actualControlledCount (compensatedPrefixControl pc) rhi
  let Ue := (Phi^[Ce]) B
  let Uc := (Phi^[Cc]) B
  have hd := actualSuccessorMassResidualAlgebra gamma hg he B c e hce heB hbudget
  have htheta : theta < epsilonZero := (Ordinal.le_mul_left theta Ordinal.omega0_pos).trans_lt he
  have hre : re < theta := hd.2.2.2.1
  have hrhi : rhi < L := hd.2.2.2.2.1
  have heqE : pe+actualOrdinalNorm re=B := hd.2.2.2.2.2.2.2.1
  have heqC : pc+actualOrdinalNorm rhi=B := hd.2.2.2.2.2.2.2.2.1
  have hsync := actualCompensatedSynchronizedTraces pe pc re rhi hd.2.2.2.2.2.1
    (hrhi.trans he) hd.2.2.2.2.2.2.1 (by rw [heqE, heqC])
  have hCC : Ce ≤ Cc := hsync.1
  have hBU : B ≤ Ue := by
    have hh := iterate_index_mono (fun n => (self_lt_Phi n).le) B (Nat.zero_le Ce)
    simpa only [Function.iterate_zero_apply] using hh
  have hUU : Ue ≤ Uc := iterate_index_mono (fun n => (self_lt_Phi n).le) B hCC
  have hrE : re < Ordinal.omega0^(gamma+1) := by
    rw [Ordinal.opow_add_one]
    exact hre.trans_le (Ordinal.le_mul_left theta Ordinal.omega0_pos)
  have hrC : rhi < Ordinal.omega0^(gamma+1) := by rw [Ordinal.opow_add_one]; exact hrhi
  have hcutE := actualCompensatedPrincipalRetainedCut gamma hg htheta q e B re (hre.trans htheta) hrE heqE
  have hcutC := actualCompensatedPrincipalRetainedCut gamma hg htheta q c B rhi (hrhi.trans he) hrC heqC
  have hAE : theta*(q : Ordinal)+re=Alo := hd.2.2.2.2.2.2.2.2.2.1
  have hAC : theta*(q : Ordinal)+rhi=Ahi := hd.2.2.2.2.2.2.2.2.2.2
  dsimp only at hcutE hcutC
  rw [hAE] at hcutE
  rw [hAC] at hcutC
  exact ⟨hCC, hBU, hUU, hcutE.1, hcutC.1, hcutE.2.1, hcutC.2.1,
    hcutE.2.2.1, hcutC.2.2.1, hcutE.2.2.2.2, hcutC.2.2.2.2⟩

end LogicLineages.OrdinalComparison
