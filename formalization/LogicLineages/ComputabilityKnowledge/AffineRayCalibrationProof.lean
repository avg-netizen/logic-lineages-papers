module

public import LogicLineages.ComputabilityKnowledge.AffineRayCalibrationBasics
public import LogicLineages.ComputabilityKnowledge.AffineRayCalibrationEffectivity
public import LogicLineages.ModelsAlgebra.Differential.KroneckerIndex

@[expose] public section

/-! Direct Codex completion of the frozen affine-ray supplier after the
managed author launch was refused before initialization by its admission
deadline. No Claude candidate or author process is claimed for this round.
-/
namespace LogicLineages.ComputabilityKnowledge.AffineRayCalibrationProof

open ExponentialNormalForm ExponentialNormalFormCodec AffineRayCalibration
open AffineRayCalibrationBasics

theorem slope_inj (d : Nat) (family : List CoeffCode) (a b : CoeffCode)
    (ha : a ∈ withZero family) (hb : b ∈ withZero family) :
    slope d family a = slope d family b ↔
      ∀ i : Fin d, coeffDecode d a i.succ = coeffDecode d b i.succ := by
  have hp := positiveCalibration d family
  have hindex (c : CoeffCode) :
      LogicLineages.ModelsAlgebra.Differential.KroneckerIndex.index (rayBase family)
        (fun i : Fin d => coeffDecode d c i.succ) = slope d family c := by
    rw [slope_sum]
    unfold LogicLineages.ModelsAlgebra.Differential.KroneckerIndex.index
    apply Finset.sum_congr rfl
    intro i _
    rw [weight_at]
  constructor
  · intro heq
    have hi := LogicLineages.ModelsAlgebra.Differential.KroneckerIndex.index_injective
      d (rayBase family) hp.1 (fun i => coeffDecode d a i.succ)
      (fun i => coeffDecode d b i.succ)
      (fun i => hp.2.2.2.2 a ha i.succ) (fun i => hp.2.2.2.2 b hb i.succ)
      (by rw [hindex, hindex, heq])
    exact fun i => congrFun hi i
  · intro heq
    rw [slope_sum, slope_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [heq i]

theorem slopeCalibration : Comparators.AffineRayCalibration.SlopeCalibration := by
  intro d family
  exact ⟨slope_sum d family, fun a ha b hb => slope_inj d family a b ha hb⟩

private theorem slope_gap (A B t : Nat) (h : A < B) : A * t + t ≤ B * t := by
  have hm := Nat.mul_le_mul_right t (Nat.succ_le_of_lt h)
  simpa only [Nat.succ_mul] using hm

private theorem numeric_order (A B c e t : Nat) (hc : c < t) (he : e < t) :
    (if A = B then c < e else A < B) ↔ c + A * t < e + B * t := by
  by_cases hab : A = B
  · simp only [hab, ↓reduceIte]
    omega
  · simp only [hab, ↓reduceIte]
    rcases Nat.lt_or_gt_of_ne hab with hlt | hgt
    · have hm := slope_gap A B t hlt
      constructor <;> intro h <;> omega
    · have hm := slope_gap B A t hgt
      constructor <;> intro h <;> omega

private theorem numeric_equality (A B c e t : Nat) (hc : c < t) (he : e < t)
    (h : c + A * t = e + B * t) : A = B ∧ c = e := by
  by_cases hab : A = B
  · constructor
    · exact hab
    · rw [hab] at h
      omega
  · rcases Nat.lt_or_gt_of_ne hab with hlt | hgt
    · have hm := slope_gap A B t hlt
      omega
    · have hm := slope_gap B A t hgt
      omega

theorem computedEventualComparison : Comparators.AffineRayCalibration.ComputedEventualComparison := by
  intro d family a ha b hb t ht
  have hca : a.getD 0 0 < t := by
    have hm := coefficient_le_family ha 0
    unfold cutoff at ht
    omega
  have hcb : b.getD 0 0 < t := by
    have hm := coefficient_le_family hb 0
    unfold cutoff at ht
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [affineRayEvaluation, affineRayEvaluation]
    have hn := numeric_order (slope d family a) (slope d family b)
      (a.getD 0 0) (b.getD 0 0) t hca hcb
    by_cases hab : slope d family a = slope d family b
    · simpa only [rayCompare, hab, ↓reduceIte, decide_eq_true_eq] using hn
    · simpa only [rayCompare, hab, ↓reduceIte, decide_eq_true_eq] using hn
  · constructor
    · intro hv
      rw [affineRayEvaluation, affineRayEvaluation] at hv
      have heq := numeric_equality _ _ _ _ _ hca hcb hv
      have hvars := (slope_inj d family a b ha hb).mp heq.1
      funext i
      exact Fin.cases heq.2 hvars i
    · intro heq
      rw [heq]
  · intro i
    have hp := (positiveCalibration d family).2.2.2.1 i
    have hpos : 0 < t := by unfold cutoff at ht; omega
    exact Nat.mul_pos hp.2 hpos

theorem constantFreeGap : Comparators.AffineRayCalibration.ConstantFreeGap := by
  intro d family a ha b hb hca hcb hne t
  have hslopes : slope d family a ≠ slope d family b := by
    intro heq
    have hvars := (slope_inj d family a b ha hb).mp heq
    apply hne
    funext i
    refine Fin.cases ?_ hvars i
    change a.getD 0 0 = b.getD 0 0
    omega
  rw [affineRayEvaluation, affineRayEvaluation, hca, hcb]
  simp only [zero_add]
  constructor
  · intro htrue
    have hlt : slope d family a < slope d family b := by
      simpa only [rayCompare, hslopes, ↓reduceIte, decide_eq_true_eq] using htrue
    exact slope_gap _ _ _ hlt
  · intro hfalse
    have hnlt : ¬ slope d family a < slope d family b := by
      simpa only [rayCompare, hslopes, ↓reduceIte, decide_eq_false_iff_not] using hfalse
    have hlt : slope d family b < slope d family a := by omega
    exact slope_gap _ _ _ hlt

theorem affineRayCalibration : Comparators.AffineRayCalibration.Target :=
  ⟨positiveCalibration, slopeCalibration, affineRayEvaluation,
    computedEventualComparison, constantFreeGap,
    AffineRayCalibrationEffectivity.actualPrimitivePrograms⟩

end LogicLineages.ComputabilityKnowledge.AffineRayCalibrationProof
