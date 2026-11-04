module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovInverseTargets
public import LogicLineages.OrdinalComparison.FixedSeedControlResidueGrowthProof
public import LogicLineages.OrdinalComparison.FixedSeedControlResidueProgramsProof
public import LogicLineages.OrdinalComparison.ControlHierarchyGrowthProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovInverse.Proof
open FixedSeedControlResidue

private theorem upper {g : Nat → Nat} (hg : ∀ n, n < g n) (x : Nat) :
    x < g (floorInverse g x + 1) := by
  by_contra h
  have hp : g (floorInverse g x + 1) ≤ x := Nat.le_of_not_gt h
  have hb : floorInverse g x + 1 ≤ x := (hg _).le.trans hp
  exact (Nat.findGreatest_is_greatest (P := fun n => g n ≤ x)
    (show floorInverse g x < floorInverse g x + 1 by omega) hb) hp

private theorem lower {g : Nat → Nat} (hm : Monotone g)
    (hg : ∀ n, n < g n) (x n : Nat) (hn : 0 < n) :
    n ≤ floorInverse g x ↔ g n ≤ x := by
  constructor
  · intro h
    have hpos : floorInverse g x ≠ 0 := by omega
    have hs := Nat.findGreatest_of_ne_zero
      (P := fun k => g k ≤ x) (show Nat.findGreatest (fun k => g k ≤ x) x =
        floorInverse g x from rfl) hpos
    exact (hm h).trans hs
  · intro h
    exact Nat.le_findGreatest ((hg n).le.trans h) h

private theorem below {g : Nat → Nat} (hm : Monotone g)
    (hg : ∀ n, n < g n) (x n : Nat) (hn : 0 < n) :
    floorInverse g x < n ↔ x < g n := by
  have h := lower hm hg x n hn
  omega

private theorem graph {g : Nat → Nat} (hm : StrictMono g)
    (hg : ∀ n, n < g n) : FloorGraph g (floorInverse g) := by
  intro x n
  constructor
  · intro h
    subst n
    refine ⟨?_, upper hg x⟩
    by_cases hz : floorInverse g x = 0
    · exact Or.inl hz
    · exact Or.inr ((lower hm.monotone hg x _ (by omega)).mp le_rfl)
  · rintro ⟨hlo, hup⟩
    have hle : n ≤ floorInverse g x := by
      rcases hlo with hz | h
      · omega
      · by_cases hn : n = 0
        · omega
        · exact (lower hm.monotone hg x n (by omega)).mpr h
    have hlt : floorInverse g x < n + 1 :=
      (below hm.monotone hg x (n + 1) (by omega)).mpr hup
    omega

private theorem mono (g : Nat → Nat) : Monotone (floorInverse g) := by
  intro x y hxy
  exact Nat.findGreatest_mono (fun _ h => h.trans hxy) hxy

private theorem roundtrip {g : Nat → Nat} (hm : StrictMono g)
    (hg : ∀ n, n < g n) (n : Nat) : floorInverse g (g n) = n :=
  (graph hm hg (g n) n).mpr ⟨Or.inr le_rfl, hm (by omega)⟩

private theorem zero (g : Nat → Nat) : floorInverse g 0 = 0 := by
  exact Nat.eq_zero_of_le_zero (Nat.findGreatest_le 0)

private theorem two_power_growth {g : Nat → Nat}
    (hd : ∀ n, 2 * g n ≤ g (n + 1)) (n a : Nat) :
    2 ^ a * g n ≤ g (n + a) := by
  induction a with
  | zero => simp
  | succ a ih =>
    calc
      2 ^ (a + 1) * g n = 2 * (2 ^ a * g n) := by
        simp only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ 2 * g (n + a) := Nat.mul_le_mul_left 2 ih
      _ ≤ g (n + a + 1) := hd _
      _ = g (n + (a + 1)) := by rw [Nat.add_assoc]

private theorem compression {g : Nat → Nat} (hm : Monotone g)
    (hg : ∀ n, n < g n) (hd : ∀ n, 2 * g n ≤ g (n + 1))
    (a x : Nat) : floorInverse g (a * x) ≤ floorInverse g x + a := by
  by_cases ha : a = 0
  · subst a
    simp only [Nat.zero_mul, zero, Nat.add_zero, Nat.zero_le]
  · have hpos : 0 < a := by omega
    have hstrict : a * x < g (floorInverse g x + 1 + a) := by
      calc
        a * x < a * g (floorInverse g x + 1) :=
          Nat.mul_lt_mul_of_pos_left (upper hg x) hpos
        _ ≤ 2 ^ a * g (floorInverse g x + 1) :=
          Nat.mul_le_mul_right _ (Nat.lt_two_pow_self.le)
        _ ≤ g (floorInverse g x + 1 + a) := two_power_growth hd _ _
    have h := (below hm hg (a * x) (floorInverse g x + 1 + a)
      (by omega)).mpr hstrict
    omega

private theorem phi_doubling (n : Nat) : 2 * Phi n ≤ Phi (n + 1) :=
  fullFastControlHierarchyGrowth.2.2 0 n (Nat.zero_le n)

private theorem phi_linear (n : Nat) : 2 * n ≤ Phi n := by
  calc
    2 * n ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 (Nat.lt_two_pow_self.le)
    _ = 2 ^ (n + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    _ ≤ 2 ^ (n + 100) := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ Phi n := two_pow_shift_le_Phi n

private theorem h_doubling (n : Nat) : 2 * H n ≤ H (n + 1) := by
  rw [FixedSeedControlResidue.Proof.h_succ]
  exact phi_linear _

private theorem h_growth (n : Nat) : n < H n := by
  have h := FixedSeedControlResidue.Proof.h_lower_bound n
  omega

theorem exactOriginalGraphs : Targets.ExactOriginalGraphs :=
  ⟨graph Phi_strictMono self_lt_Phi,
    graph FixedSeedControlResidue.Proof.h_strictMono h_growth⟩

theorem originalOrderAndRoundTrips : Targets.OriginalOrderAndRoundTrips := by
  refine ⟨?_, zero Phi, zero H, mono Phi, mono H, ?_, ?_⟩
  · intro n
    exact ⟨roundtrip Phi_strictMono self_lt_Phi n,
      roundtrip FixedSeedControlResidue.Proof.h_strictMono h_growth n⟩
  · intro x
    exact ⟨Nat.findGreatest_le x, Nat.findGreatest_le x⟩
  · intro x n hn
    exact ⟨below Phi_strictMono.monotone self_lt_Phi x n hn,
      lower Phi_strictMono.monotone self_lt_Phi x n hn,
      below FixedSeedControlResidue.Proof.h_strictMono.monotone h_growth x n hn,
      lower FixedSeedControlResidue.Proof.h_strictMono.monotone h_growth x n hn⟩

theorem effectiveCoefficientCompression : Targets.EffectiveCoefficientCompression := by
  intro a x
  exact ⟨compression Phi_strictMono.monotone self_lt_Phi phi_doubling a x,
    compression FixedSeedControlResidue.Proof.h_strictMono.monotone
      h_growth h_doubling a x⟩

private theorem primitive_floor {g : Nat → Nat} (hg : Primrec g) :
    Primrec (floorInverse g) := by
  exact Primrec.nat_findGreatest Primrec.id
    (Primrec.nat_le.comp (hg.comp Primrec.snd) Primrec.fst)

theorem actualPrimitiveRecursion : Targets.ActualPrimitiveRecursion :=
  ⟨primitive_floor Phi_primrec,
    primitive_floor FixedSeedControlResidue.Proof.H_primitive, Primrec.id⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovInverse.Proof
