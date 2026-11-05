module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherIndexTargets
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherProductProof
public import Mathlib.Data.Nat.ModEq

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherIndexArithmeticProof
open Cipher CipherIndex CipherIndexTargets
open scoped BigOperators

private theorem evenMulCongruence (c x y k : Nat) (hc : 2 ∣ c)
    (h : Nat.ModEq (2^k) x y) : Nat.ModEq (2^(k+1)) (x*c) (y*c) := by
  have hc' : (2 : Int) ∣ (c : Int) := Int.ofNat_dvd.mpr hc
  apply Nat.modEq_of_dvd
  have hd := mul_dvd_mul h.dvd hc'
  have he : (y : Int)*c-(x : Int)*c=((y : Int)-x)*c := by ring
  simpa only [Nat.pow_succ, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, he] using hd

theorem evenMaskedProductFixedPointUnique : EvenMaskedProductFixedPointUnique := by
  intro A B c w x y hc hxe hye
  have hm : ∀ k : Nat, Nat.ModEq (2^k) x y := by
    intro k
    induction k with
    | zero => change x%1=y%1; omega
    | succ k ih =>
        have hs := evenMulCongruence c x y k hc ih
        have ha : Nat.ModEq (2^(k+1)) ((x*c) &&& w) ((y*c) &&& w) := by
          dsimp [Nat.ModEq] at hs ⊢
          rw [Nat.and_mod_two_pow, Nat.and_mod_two_pow, hs]
        have hh := ha.add_left A
        rw [hxe, hye] at hh
        exact hh.add_right_cancel' B
  have hp := (x+y+1).lt_two_pow_self
  have hpx : x < 2^(x+y+1) := by omega
  have hpy : y < 2^(x+y+1) := by omega
  have h := hm (x+y+1)
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt hpx, Nat.mod_eq_of_lt hpy] using h

private theorem indexBounded (n q : Nat) (hq : n+1<q) : Bounded n q id := by
  intro i hi
  have h : q<2^q := Nat.lt_two_pow_self
  dsimp
  omega

private theorem onesBounded (n q : Nat) (hq : n+1<q) : Bounded n q (fun _ => 1) := by
  intro i hi
  have h : 2^0<2^q := Nat.pow_lt_pow_right (by decide : 1<2) (by omega)
  simpa using h

private theorem onesEven (n q : Nat) (hq : n+1<q) : 2 ∣ ones n q := by
  have hb : 2 ∣ base q := by
    refine ⟨2^(4*q-1), ?_⟩
    have he : 4*q=1+(4*q-1) := by omega
    rw [base, he, Nat.pow_add]
    simp
  unfold ones encode
  apply Finset.dvd_sum
  intro i hi
  simp only [Nat.one_mul]
  have he : 0<2^(i+1) := Nat.two_pow_pos _
  obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
  rw [hl, Nat.pow_succ]
  exact dvd_mul_of_dvd_right hb _

private theorem indexShift (n q : Nat) :
    shiftedEncode n q id+shiftedOnes n q = index n q+n*(base q)^(2^(n+1)) := by
  induction n with
  | zero => simp [shiftedEncode, shiftedOnes, index, encode]
  | succ n ih =>
      simp only [shiftedEncode, shiftedOnes, index, encode, Finset.sum_range_succ,
        id_eq, Nat.one_mul] at ih ⊢
      rw [show n+1+1=n+2 by omega]
      nlinarith [ih]

private theorem indexSatisfies (n q : Nat) (hq : n+1<q) : IndexEquations n q (index n q) := by
  have hp := CipherProductProof.cipherProductMask n q id (fun _ => 1) hq
    (indexBounded n q hq) (onesBounded n q hq)
  change ((index n q*ones n q) &&& ((base q-1)*shiftedOnes n q)) =
    shiftedEncode n q (fun i => i*1) at hp
  simp only [Nat.mul_one] at hp
  refine ⟨hq, ?_⟩
  rw [hp]
  exact indexShift n q

theorem indexArithmeticCharacterization : IndexArithmeticCharacterization := by
  intro n q a
  constructor
  · rintro ⟨hq,rfl⟩
    exact indexSatisfies n q hq
  · intro h
    have hi := indexSatisfies n q h.1
    refine ⟨h.1, ?_⟩
    exact evenMaskedProductFixedPointUnique (shiftedOnes n q)
      (n*(base q)^(2^(n+1))) (ones n q) ((base q-1)*shiftedOnes n q)
      a (index n q) (onesEven n q h.1) (by simpa only [Nat.add_comm] using h.2)
        (by simpa only [Nat.add_comm] using hi.2)

theorem isCipherOfIndex_iff (n q a : Nat) :
    IsCipherOf n q id a ↔ n+1<q ∧ a=index n q := by
  constructor
  · rintro ⟨hq,_,he⟩
    exact ⟨hq,he⟩
  · rintro ⟨hq,he⟩
    exact ⟨hq,indexBounded n q hq,he⟩

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherIndexArithmeticProof
