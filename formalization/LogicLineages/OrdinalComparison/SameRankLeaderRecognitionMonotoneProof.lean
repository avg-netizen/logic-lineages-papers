module
public import LogicLineages.OrdinalComparison.SameRankLeaderRecognitionTargets
public import LogicLineages.OrdinalComparison.CounterLeaderExpansionEntriesProof
public import LogicLineages.OrdinalComparison.SuffixKernelMonotoneProof
public import LogicLineages.OrdinalComparison.ConstantCutFactsProof
public import LogicLineages.OrdinalComparison.PolynomialPartitionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SameRankLeaderRecognition.Proof
open CounterLeaderExpansion

private theorem kernel_fixed_strict (d c t u : Nat) (hd : 1 ≤ d)
    (ht : c+d+1 ≤ t) (hu : c+d+1 ≤ u) (htu : t < u) :
    kernel d c t < kernel d c u := by
  have hpos : (0 : Ordinal) < (d : Ordinal) := by
    exact_mod_cast (show 0 < d by omega)
  have hnorm : actualOrdinalNorm (Ordinal.omega0 ^ (d : Ordinal)) = d+1 := by
    simpa only [Nat.cast_one, mul_one, Nat.mul_one] using
      (actualFiniteMonomialFacts d 1).2.1
  have hdt : c + actualOrdinalNorm (Ordinal.omega0 ^ (d : Ordinal)) ≤ t := by
    rw [hnorm]
    omega
  have hdu : c + actualOrdinalNorm (Ordinal.omega0 ^ (d : Ordinal)) ≤ u := by
    rw [hnorm]
    omega
  exact actualSuffixKernelStrictInput (d : Ordinal) hpos
    (finiteOmegaPowerBelowEpsilonZero d) c c t u le_rfl htu hdt hdu

private theorem bottomInput_fixed_strict (n c t u : Nat)
    (ht : threshold n c ≤ t) (hu : threshold n c ≤ u) (htu : t < u) :
    bottomInput n c t < bottomInput n c u := by
  induction n generalizing t u with
  | zero => exact htu
  | succ n ih =>
    have hdt : (c+n+4)+(n+4)+1 ≤ t := by
      dsimp [threshold] at ht
      omega
    have hdu : (c+n+4)+(n+4)+1 ≤ u := by
      dsimp [threshold] at hu
      omega
    have hk := kernel_fixed_strict (n+4) (c+n+4) t u (by omega) hdt hdu htu
    have hkt := CounterLeaderExpansion.Proof.kernel_ge (n+4) (c+n+4) t
    have hku := CounterLeaderExpansion.Proof.kernel_ge (n+4) (c+n+4) u
    have htailt : threshold n c ≤ kernel (n+4) (c+n+4) t := by
      dsimp [threshold] at ht ⊢
      omega
    have htailu : threshold n c ≤ kernel (n+4) (c+n+4) u := by
      dsimp [threshold] at hu ⊢
      omega
    exact ih _ _ htailt htailu hk

/-- The original expansion tail suffices throughout the literal descending
kernel chain, including the final cubic kernel and its Phi image. -/
theorem actualFixedRankStrictInputs : Targets.ActualFixedRankStrictInputs := by
  intro n c t u ht hu htu
  have hb := bottomInput_fixed_strict n c t u ht hu htu
  have hbt := CounterLeaderExpansion.Proof.bottomInput_ge n c t
  have hbu := CounterLeaderExpansion.Proof.bottomInput_ge n c u
  have hdt : (c+3)+3+1 ≤ bottomInput n c t := by
    dsimp [threshold] at ht
    omega
  have hdu : (c+3)+3+1 ≤ bottomInput n c u := by
    dsimp [threshold] at hu
    omega
  have hp := kernel_fixed_strict 3 (c+3) (bottomInput n c t) (bottomInput n c u)
    (by omega) hdt hdu hb
  exact ⟨hb, hp, Phi_strictMono hp⟩

end LogicLineages.OrdinalComparison.SameRankLeaderRecognition.Proof
