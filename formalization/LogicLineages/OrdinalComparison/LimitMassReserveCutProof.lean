module
public import LogicLineages.OrdinalComparison.LimitMassReserveCutTargets
public import LogicLineages.OrdinalComparison.LimitMassPackedProof
public import LogicLineages.OrdinalComparison.SuccessorKernelCutProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem limitmass_cut_nat_norm (n : Nat) : actualOrdinalNorm (n : Ordinal)=n := by
  have h := actualOrdinalNorm_notationCorrespondence (NONote.ofNat n)
  rw [norm_ofNat] at h
  change actualOrdinalNorm (ONote.ofNat n).repr=n at h
  simpa only [ONote.repr_ofNat] using h

private theorem limitmass_retained_cut (gamma : Ordinal.{0}) (hg : 0 < gamma)
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
    rw [hm, limitmass_cut_nat_norm]
  have hpV : p ≤ V := by omega
  have hmeq : m=V-p := by omega
  refine ⟨hcount.1, htrace.1, hpV, Nat.sub_add_cancel hpV, ?_⟩
  rw [htrace.1 q le_rfl, hm, hmeq]

theorem actualLimitMassReserveCut : Targets.ActualLimitMassReserveCut := by
  intro L beta hl hL E hv t c e hT hce he
  dsimp only
  let B := Phi t
  let C := Phi B
  let pe := actualMaximumPredecessor L.1.repr (B-e)
  let R := profileReserveBlocks (profileBoundWord E)
  let p := c+R*actualOrdinalNorm pe
  let k := C-(c+(R+1)*actualOrdinalNorm pe)
  let r := pe+(k : Ordinal)
  let A := pe*(R : Ordinal)+r
  let D := actualSuffixKernelCount L.1.repr e t
  let Z := actualSuffixKernel L.1.repr e t
  let q := actualControlledCount (compensatedPrefixControl p) r
  let V := (Phi^[q]) C
  have hf := actualLimitMassFirstSuffixes L beta hl hL E hv t c e hT hce he
  have hpack := actualLimitMassPackedState L beta hl hL E hv t c e hT hce he
  have hpeE : pe < epsilonZero := (hf.2.1.trans hf.2.2.1).trans (normalRepresentationSound L)
  have hr := actualFiniteTailClosureNorm pe hpeE k
  have hlow : e+actualOrdinalNorm pe=B := hf.2.2.2.2.2.1
  have htotal : p+actualOrdinalNorm r=C := hpack.2.2.2.2.2.2.2.1
  have hsync := actualCompensatedSynchronizedTraces e p pe r le_self_add hr.1
    (by rw [hr.2]; exact Nat.le_add_right _ _) (by
      change e+actualOrdinalNorm pe ≤ p+actualOrdinalNorm r
      rw [hlow, htotal]
      exact (self_lt_Phi B).le)
  have hel : Ordinal.omega0^beta < epsilonZero := by rw [← hL]; exact normalRepresentationSound L
  have hfirst := actualSuffixKernelFirstMaximum beta hl.bot_lt hel e t (by rw [← hL]; exact he)
  have hD : D=actualControlledCount (compensatedPrefixControl e) pe+1 := by
    simpa only [← hL] using hfirst.2.1
  have hDpos : 0 < D := by omega
  have hDq : D ≤ q+1 := by
    have hc := hsync.1
    change actualControlledCount (compensatedPrefixControl e) pe ≤ q at hc
    omega
  obtain ⟨gamma, hg, hpe⟩ := hf.2.2.2.2.2.2.2.1
  change pe=Ordinal.omega0^gamma at hpe
  have hpow : Ordinal.omega0^gamma < epsilonZero := by rw [← hpe]; exact hpeE
  have hrbound : r < Ordinal.omega0^(gamma+1) := by
    have hp : pe < Ordinal.omega0^(gamma+1) := by
      rw [hpe]
      exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (Order.lt_add_one_iff.mpr le_rfl)
    have hk : (k : Ordinal) < Ordinal.omega0^(gamma+1) :=
      (Ordinal.natCast_lt_omega0 k).trans_le (by
        simpa only [Ordinal.opow_one] using Ordinal.opow_le_opow_right Ordinal.omega0_pos
          (show (1 : Ordinal) ≤ gamma+1 from le_add_self))
    exact Ordinal.isPrincipal_add_omega0_opow (gamma+1) hp hk
  have hcut := limitmass_retained_cut gamma hg hpow R c C r hr.1 hrbound (by rw [← hpe]; exact htotal)
  rw [← hpe] at hcut
  have hR : R+4 ≤ t := (max_le_iff.mp (max_le_iff.mp hT).2).1
  have hBZ : B ≤ Z := by
    change Phi t ≤ (Phi^[D]) t
    have hi := iterate_index_mono (fun n => (self_lt_Phi n).le) t (show 1 ≤ D by omega)
    simpa only [Function.iterate_one] using hi
  have hpZ : p ≤ (R+1)*Z := hpack.2.2.2.2.2.2.2.2.trans (Nat.mul_le_mul_left (R+1) hBZ)
  have hgap := actualLimitMassNumericalGap R t D q p hR hDpos hDq hpZ
  exact ⟨hDpos, hDq, hcut.1, hcut.2.1, hcut.2.2.1, hcut.2.2.2.1, hcut.2.2.2.2, hgap⟩

end LogicLineages.OrdinalComparison
