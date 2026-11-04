module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovHyperCollisionTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovInverseProof
public import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovHyperCollision.Proof
open FixedSeedControlResidue
open SnyatkovInverse
open IntegerAlgorithms.Proof

private theorem linear (n : Nat) : 2 * n ≤ Phi n := by
  calc
    2 * n ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 (Nat.lt_two_pow_self.le)
    _ = 2 ^ (n + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    _ ≤ 2 ^ (n + 100) := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ Phi n := two_pow_shift_le_Phi n

theorem actualCoefficientElimination : Targets.ActualCoefficientElimination := by
  intro a b c h
  have hi := SnyatkovInverse.Proof.originalOrderAndRoundTrips
  have hmono := hi.2.2.2.1 h
  have hbound := (SnyatkovInverse.Proof.effectiveCoefficientCompression c (Phi b)).1
  rw [(hi.1 a).1] at hmono
  rw [(hi.1 b).1] at hbound
  exact hmono.trans hbound

private theorem absolute_bounds (z : Int) :
    -(z.natAbs : Int) ≤ z ∧ z ≤ (z.natAbs : Int) := by
  constructor
  · have h := Int.le_natAbs (a := -z)
    simpa only [Int.natAbs_neg, neg_neg] using (neg_le_neg h)
  · exact Int.le_natAbs

private theorem domains (c : Nat) (e k : Int) (u v : Nat)
    (hv : collisionBound c e k ≤ v) (hvu : v ≤ u) :
    0 ≤ (H u : Int) + e ∧ 0 ≤ (H v : Int) + k ∧
    (shiftedInput u e : Int) = (H u : Int) + e ∧
    (shiftedInput v k : Int) = (H v : Int) + k := by
  have huH := FixedSeedControlResidue.Proof.h_lower_bound u
  have hvH := FixedSeedControlResidue.Proof.h_lower_bound v
  have he := absolute_bounds e
  have hk := absolute_bounds k
  unfold collisionBound at hv
  have he0 : 0 ≤ (H u : Int) + e := by omega
  have hk0 : 0 ≤ (H v : Int) + k := by omega
  exact ⟨he0, hk0, Int.toNat_of_nonneg he0, Int.toNat_of_nonneg hk0⟩

theorem finiteWindowAndDomains : Targets.FiniteWindowAndDomains := by
  refine ⟨?_, domains⟩
  intro c e k u v hvu hcomp
  by_contra hbound
  have hv : collisionBound c e k ≤ v := Nat.le_of_not_gt hbound
  obtain ⟨_, _, heq, hkq⟩ := domains c e k u v hv hvu.le
  have hc := actualCoefficientElimination (shiftedInput u e) (shiftedInput v k) c hcomp
  have hstep : 2 * H v ≤ H u := by
    calc
      2 * H v ≤ Phi (H v) := linear _
      _ = H (v + 1) := (FixedSeedControlResidue.Proof.h_succ v).symm
      _ ≤ H u := FixedSeedControlResidue.Proof.h_strictMono.monotone (by omega)
  have hvH := FixedSeedControlResidue.Proof.h_lower_bound v
  have he := absolute_bounds e
  have hk := absolute_bounds k
  unfold collisionBound at hv
  omega

private theorem toNat_primitive : Primrec Int.toNat := by
  apply (Primrec.ite
    (Primrec.eq.comp sign_primitive (Primrec.const (-1 : Int)))
    (Primrec.const 0) abs_primitive).of_eq
  intro z
  cases z with
  | ofNat n => cases n <;> rfl
  | negSucc n => rfl

private theorem shifted_primitive : Primrec₂ shiftedInput :=
  toNat_primitive.comp (add_primitive.comp
    (ofNat_primitive.comp (FixedSeedControlResidue.Proof.H_primitive.comp Primrec.fst))
    Primrec.snd)

theorem actualPrimitiveRecursion : Targets.ActualPrimitiveRecursion := by
  refine ⟨shifted_primitive, Phi_primrec.comp shifted_primitive, ?_⟩
  exact Primrec.nat_add.comp
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp Primrec.fst
        (abs_primitive.comp (Primrec.fst.comp Primrec.snd)))
      (abs_primitive.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.const 1)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovHyperCollision.Proof
