module
public import LogicLineages.OrdinalComparison.CollectedAffineBandTargets
public import LogicLineages.OrdinalComparison.CollectedPeakProof
public import LogicLineages.OrdinalComparison.LimitMassNumericProof
public import Mathlib.Tactic.Linarith

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem square_le_power (n : Nat) (hn : 4≤n) : n*n≤2^n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have hpoly : (n+1)*(n+1)≤2*(n*n) := by nlinarith
    calc
      (n+1)*(n+1)≤2*(n*n) := hpoly
      _≤2*2^n := Nat.mul_le_mul_left 2 ih
      _=2^(n+1) := by rw [Nat.pow_succ,Nat.mul_comm]

theorem phiMultiplicativeStepGap : Targets.PhiMultiplicativeStepGap := by
  intro s k hk
  have hfour := four_le_Phi s
  have hky : k<Phi s := hk.trans_lt (self_lt_Phi s)
  calc
    k*Phi s<Phi s*Phi s := Nat.mul_lt_mul_of_pos_right hky (by omega)
    _≤2^(Phi s) := square_le_power _ hfour
    _≤2^(2^Phi s) := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt Nat.lt_two_pow_self)
    _≤Phi (s+1) := Phi_double_tower_gap s

theorem phiBetweenImagesRoot : Targets.PhiBetweenImagesRoot := by
  intro s n hlo hhi
  rintro ⟨k,hk⟩
  by_cases hks : k≤s
  · have h := Phi_strictMono.monotone hks
    rw [hk] at h
    omega
  · have h := Phi_strictMono.monotone (show s+1≤k by omega)
    rw [hk] at h
    omega

theorem collectedAffineInputBand : Targets.CollectedAffineInputBand := by
  intro rho c b hl he hb
  have hT : collectedAffineThreshold rho c b=max 4 (actualOrdinalNorm rho.1.repr+c+b+1) := by
    rw [actualOrdinalNorm_notationCorrespondence rho]
    rfl
  refine ⟨hT,?_⟩
  intro x hx
  rw [hT] at hx
  have hx4 : 4≤x := (le_max_left _ _).trans hx
  have hab : actualOrdinalNorm rho.1.repr+c+b≤x := by
    have h := (le_max_right _ _).trans hx
    omega
  have hn := collectedAtomNormDecomposition rho c b .nil hl he x
  simp only [actualCollectedTagsEval,Nat.add_zero] at hn
  rw [hn]
  constructor
  · have h := Nat.mul_le_mul_right x hb
    simp only [Nat.one_mul] at h
    omega
  · have ha := Nat.mul_le_mul_left (actualOrdinalNorm rho.1.repr+c) (show 1≤x by omega)
    simp only [Nat.mul_one] at ha
    calc
      actualOrdinalNorm rho.1.repr+c+b*x≤(actualOrdinalNorm rho.1.repr+c)*x+b*x := Nat.add_le_add_right ha _
      _=(actualOrdinalNorm rho.1.repr+c+b)*x := (Nat.add_mul _ _ _).symm
      _≤x*x := Nat.mul_le_mul_right x hab
      _<Phi x := actualPhiSquareGap x

end LogicLineages.OrdinalComparison
