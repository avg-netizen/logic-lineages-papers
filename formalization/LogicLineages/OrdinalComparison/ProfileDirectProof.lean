module
public import LogicLineages.OrdinalComparison.ProfileDirectTargets
public import LogicLineages.OrdinalComparison.ProfileDirectPackedProof
public import LogicLineages.OrdinalComparison.KernelTransportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualUniformProfileDirectGrowth : Targets.ActualUniformProfileDirectGrowth := by
  intro L hprincipal hlarge E hv t c hT hc
  have hpacked := actualProfileDirectPackedState L hprincipal hlarge E hv t c hT hc
  let word := profileBoundWord E
  let R := profileReserveBlocks word
  let pi := (profilePrincipalDominator word).1.repr
  let S := pi * (R : Ordinal) + (t : Ordinal)
  let Q := actualMaximumPredecessor L.1.repr (Phi t-c)
  let g := compensatedPrefixControl c
  have hcompiler := actualProfileBoundCompiler L.1.repr hlarge E hv
  have hdom := actualProfilePrincipalDominator L.1.repr hlarge word hcompiler.2.1
  obtain ⟨gamma, hg, hpi⟩ := hdom.2.2.2.2
  change pi = Ordinal.omega0 ^ gamma at hpi
  obtain ⟨ell, hL⟩ := hprincipal
  have heL := normalRepresentationSound L
  have hell : (1 : Ordinal) < ell := (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mp (by
    rw [Ordinal.opow_one, ← hL]
    exact hlarge)
  have hep : 0 < ell := zero_lt_one.trans hell
  have hel : Ordinal.omega0 ^ ell < epsilonZero := by rw [← hL]; exact heL
  have hreserve := fullActualEffectiveProfileReserve ell (by rw [← hL]; exact hlarge) hel E
    (by rw [← hL]; exact hv)
  have hz : fixedLimitProfileThreshold E ≤ t := (max_le_iff.mp hT).1
  have hpieps : Ordinal.omega0 ^ gamma < epsilonZero := by rw [← hpi]; exact hdom.2.2.1
  have hlead : ∀ rho ∈ word, actualProfileLeadingMonomial rho ≤ Ordinal.omega0 ^ gamma := by
    intro rho hr
    rw [← hpi]
    exact hdom.2.2.2.1 rho hr
  have hstrict := (((hreserve.2.2.2.2 t hz).2 gamma hg hpieps hlead t le_rfl).2 c)
  have hS : actualFixedLimitProfileEval E t < c + actualOrdinalNorm
      (actualControlledStateAfter g S (actualControlledCount g S)) := by
    simpa only [S, hpi] using hstrict
  have hlim := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hep)
  have hQ : Q < epsilonZero :=
    (actualMaximumPredecessor_correct L.1.repr (by rw [hL]; exact hlim.bot_lt) heL (Phi t-c)).1.1.trans heL
  have hb := compensatedPrefixControlBounds c
  have hmono := actualControlledExitNormMonotone g hb.1 (fun n => (hb.2 n).2.le)
    S Q hpacked.2.2.2.2.1 hQ hpacked.2.2.2.2.2
  have hfirst := actualSuffixKernelFirstMaximum ell hep hel c t (by rw [← hL]; exact hc)
  have hexit : actualSuffixKernel L.1.repr c t = c + actualOrdinalNorm
      (actualControlledStateAfter g Q (actualControlledCount g Q)) := by
    simpa only [← hL] using hfirst.2.2
  exact (hS.trans_le (Nat.add_le_add_left hmono c)).trans_eq hexit.symm

theorem fullActualDirectKernelGrowth : Targets.FullActualDirectKernelGrowth :=
  ⟨actualUniformProfileDirectGrowth, actualSuffixKernelBelowFixedHead⟩

end LogicLineages.OrdinalComparison
