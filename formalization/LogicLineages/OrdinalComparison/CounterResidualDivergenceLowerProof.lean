module
public import LogicLineages.OrdinalComparison.CounterResidualDivergenceTargets
public import LogicLineages.OrdinalComparison.CounterLeaderExpansionSuppliersProof
public import LogicLineages.OrdinalComparison.ControlledCountProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterResidualDivergence.Proof
open CounterLeaderExpansion

private theorem input (d a t : Nat) (hd : 1 ≤ d) (ht : a+d+1 ≤ t) :
    actualSuffixKernelInitial (Ordinal.omega0 ^ (d : Ordinal)) a t < epsilonZero ∧
    a + actualOrdinalNorm (actualSuffixKernelInitial (Ordinal.omega0 ^ (d : Ordinal)) a t) = t := by
  have hn : actualOrdinalNorm (Ordinal.omega0 ^ (d : Ordinal)) = d+1 := by
    simpa only [Nat.cast_one,mul_one,Nat.mul_one] using (actualFiniteMonomialFacts d 1).2.1
  have hp : (0 : Ordinal) < (d : Ordinal) := by exact_mod_cast (by omega : 0 < d)
  have h := actualSuffixKernelInput (d : Ordinal) hp (finiteOmegaPowerBelowEpsilonZero d)
    a t (by rw [hn]; omega)
  exact ⟨h.1,h.2.2⟩

private theorem degree_comparison (d a t : Nat) (hd : 2 ≤ d) (ht : a+d+1 ≤ t) :
    count 2 a t ≤ count d a t := by
  by_cases heq : d = 2
  · subst d; exact le_rfl
  have hin2 := input 2 a t (by omega) (by omega)
  have hind := input d a t (by omega) ht
  have hlt : actualSuffixKernelInitial (Ordinal.omega0 ^ (2 : Ordinal)) a t <
      Ordinal.omega0 ^ (d : Ordinal) := by
    have hw : Ordinal.omega0 ≤ Ordinal.omega0 ^ (2 : Ordinal) := by
      simpa only [Ordinal.opow_one] using Ordinal.opow_le_opow_right Ordinal.omega0_pos
        (show (1 : Ordinal) ≤ 2 by norm_num)
    have htail := (Ordinal.natCast_lt_omega0
      (t-a-actualOrdinalNorm (Ordinal.omega0 ^ (2 : Ordinal)))).trans_le hw
    have hdeg : (2 : Ordinal) < (d : Ordinal) := by exact_mod_cast (by omega : 2 < d)
    simpa only [actualSuffixKernelInitial,Nat.cast_one,mul_one] using
      Ordinal.opow_mul_add_lt_opow (Ordinal.natCast_lt_omega0 1) htail hdeg
  apply actualControlledCountsJointMonotone (compensatedPrefixControl a) (compensatedPrefixControl a)
    (fun _ => le_rfl) (compensatedPrefixControlBounds a).1 _ _
    (hlt.le.trans le_self_add) hind.1
  change actualOrdinalNorm (actualSuffixKernelInitial (Ordinal.omega0 ^ (2 : Ordinal)) a t) ≤
    actualOrdinalNorm (actualSuffixKernelInitial (Ordinal.omega0 ^ (d : Ordinal)) a t)
  have h2 : a + actualOrdinalNorm (actualSuffixKernelInitial (Ordinal.omega0 ^ (2 : Ordinal)) a t) = t := by
    simpa only [Nat.cast_ofNat] using hin2.2
  have hd' := hind.2
  omega

theorem actualFiniteDegreeLowerCount : Targets.ActualFiniteDegreeLowerCount := by
  refine ⟨degree_comparison,?_⟩
  intro d a K t hd ht
  have hdom : a+d+1 ≤ t := (Nat.le_max_left _ _).trans ht
  have hlarge : a+2*K+3 ≤ t := (Nat.le_max_right _ _).trans ht
  have hc := degree_comparison d a t hd hdom
  change actualSuffixKernelCount (Ordinal.omega0 ^ (2 : Ordinal)) a t ≤ count d a t at hc
  rw [CounterLeaderExpansion.Proof.quadraticCount a t (by omega)] at hc
  have hg := self_lt_Phi t
  omega

end LogicLineages.OrdinalComparison.CounterResidualDivergence.Proof
