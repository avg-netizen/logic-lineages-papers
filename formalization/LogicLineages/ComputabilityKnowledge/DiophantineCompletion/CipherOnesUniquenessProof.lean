module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherOnesUniquenessTargets
public import Mathlib.Data.Nat.ModEq

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherOnesUniquenessProof
open Cipher CipherOnesUniquenessTargets

private theorem evenSquareCongruence (x y k : Nat) (hx : 2 ∣ x) (hy : 2 ∣ y)
    (h : Nat.ModEq (2^k) x y) : Nat.ModEq (2^(k+1)) (x*x) (y*y) := by
  have hs : (2 : Int) ∣ (y : Int) + x := by
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨b+a, ?_⟩
    rw [ha, hb]
    push_cast
    ring
  apply Nat.modEq_of_dvd
  have hd := mul_dvd_mul h.dvd hs
  have he : (y : Int) * y - (x : Int) * x = ((y : Int)-x)*(y+x) := by ring
  simpa only [Nat.pow_succ, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, he] using hd

theorem evenMaskedSquareFixedPointUnique : EvenMaskedSquareFixedPointUnique := by
  intro A B w x y hx hy hxe hye
  have hm : ∀ k : Nat, Nat.ModEq (2^k) x y := by
    intro k
    induction k with
    | zero => change x%1=y%1; omega
    | succ k ih =>
        have hs := evenSquareCongruence x y k hx hy ih
        have ha : Nat.ModEq (2^(k+1)) ((x*x) &&& w) ((y*y) &&& w) := by
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

private theorem evenBasePower (q k : Nat) (hq : 0<q) (hk : 0<k) : 2 ∣ (base q)^k := by
  have hb : 2 ∣ base q := by
    refine ⟨2^(4*q-1), ?_⟩
    have he : 4*q = 1+(4*q-1) := by omega
    rw [base, he, Nat.pow_add]
    simp
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [Nat.pow_succ]
  exact dvd_mul_of_dvd_right hb _

private theorem evenSolution (n q u u1 : Nat) (hq : n+1<q)
    (hl : (base q)^2+u1 = u+(base q)^(2^(n+1)))
    (hd : (base q)^4 ∣ u1) : 2 ∣ u := by
  have hq0 : 0<q := by omega
  have h2 := Nat.mod_eq_zero_of_dvd (evenBasePower q 2 hq0 (by decide))
  have h1 := Nat.mod_eq_zero_of_dvd ((evenBasePower q 4 hq0 (by decide)).trans hd)
  have hp := Nat.mod_eq_zero_of_dvd (evenBasePower q (2^(n+1)) hq0 (Nat.two_pow_pos _))
  have hm := congrArg (fun z : Nat => z%2) hl
  simp only [Nat.add_mod, h2, h1, hp, zero_add, add_zero, Nat.zero_mod, Nat.mod_mod] at hm
  exact Nat.dvd_of_mod_eq_zero hm.symm

theorem onesEquationsAtMostOne : OnesEquationsAtMostOne := by
  intro n q u u1 v v1 hu hv
  obtain ⟨hq, hu⟩ := hu
  obtain ⟨_, hv⟩ := hv
  rcases hu with ⟨hn, hu, hu1⟩ | ⟨hn, w, u2, hw, _, hu1, _, hlu, hdu⟩
  · rcases hv with ⟨_, hv, hv1⟩ | ⟨hn', _⟩
    · exact ⟨hu.trans hv.symm, hu1.trans hv1.symm⟩
    · omega
  · rcases hv with ⟨hn', _⟩ | ⟨_, w', v2, hw', _, hv1, _, hlv, hdv⟩
    · omega
    · have hbase : 1<base q := by
        have h : 2^1 ≤ 2^(4*q) := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
        change 1 < 2^(4*q)
        omega
      have hww : w=w' := by
        apply Nat.eq_of_mul_eq_mul_left (by omega : 0<base q-1)
        omega
      subst w'
      have heu := evenSolution n q u u1 hq hlu hdu
      have hev := evenSolution n q v v1 hq hlv hdv
      have huv : u=v := evenMaskedSquareFixedPointUnique ((base q)^2)
        ((base q)^(2^(n+1))) w u v heu hev (by simpa [← hu1] using hlu)
          (by simpa [← hv1] using hlv)
      exact ⟨huv, by omega⟩

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherOnesUniquenessProof
