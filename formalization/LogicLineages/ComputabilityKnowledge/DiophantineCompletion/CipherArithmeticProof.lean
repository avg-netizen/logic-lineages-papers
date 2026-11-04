module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherArithmeticProof
open Cipher CipherTargets
open scoped BigOperators

theorem sparseNumberBound : SparseNumberBound := by
  intro n
  induction n with
  | zero =>
      intro r top e f hr hm hf ht
      simpa [sparseSum] using (Nat.pow_pos (by omega : 0<r) : 0<r^top)
  | succ n ih =>
      intro r top e f hr hm hf ht
      have hp : sparseSum n r e f < r^(e n) :=
        ih r (e n) e f hr (fun i j hij hj => hm i j hij (by omega))
          (fun i hi => hf i (by omega))
          (fun i hi => hm i n hi (Nat.lt_succ_self n))
      have hfn := hf n (Nat.lt_succ_self n)
      have hen := ht n (Nat.lt_succ_self n)
      rw [sparseSum, Finset.sum_range_succ]
      change sparseSum n r e f + f n*r^(e n) < r^top
      calc
        _ < r^(e n)+f n*r^(e n) := Nat.add_lt_add_right hp _
        _ = (f n+1)*r^(e n) := by ring
        _ ≤ r*r^(e n) := Nat.mul_le_mul_right _ (by omega)
        _ = r^(e n+1) := by rw [Nat.pow_succ]; ring
        _ ≤ r^top := Nat.pow_le_pow_right (by omega) (by omega)

theorem sparseAllDigitExtraction : SparseAllDigitExtraction := by
  intro n
  induction n with
  | zero => intro r e f hr hm hf k; simp [sparseSum]
  | succ n ih =>
      intro r e f hr hm hf k
      have hpre := ih r e f hr (fun i j hij hj => hm i j hij (by omega))
        (fun i hi => hf i (by omega))
      have hpos (j : Nat) : 0<r^j := Nat.pow_pos (by omega)
      rcases lt_trichotomy k (e n) with hk | hk | hk
      · have he : e n = k+1+(e n-k-1) := by omega
        have hpow : r^(e n) = r^k*r*r^(e n-k-1) := by
          calc
            _ = r^(k+1+(e n-k-1)) := congrArg (fun j => r^j) he
            _ = _ := by rw [Nat.pow_add, Nat.pow_add, Nat.pow_one]
        have hlast : f n*r^(e n) = r^k*(r*(f n*r^(e n-k-1))) := by rw [hpow]; ring
        rw [sparseSum, Finset.sum_range_succ]
        change ((sparseSum n r e f + f n*r^(e n))/r^k)%r = _
        rw [hlast, Nat.add_mul_div_left _ _ (hpos k), Nat.add_mul_mod_self_left,
          hpre k, Finset.sum_range_succ]
        have hne : e n≠k := by omega
        simp [hne]
      · subst k
        have hp : sparseSum n r e f < r^(e n) :=
          sparseNumberBound n r (e n) e f hr
            (fun i j hij hj => hm i j hij (by omega))
            (fun i hi => hf i (by omega))
            (fun i hi => hm i n hi (Nat.lt_succ_self n))
        have hz : (∑ i ∈ Finset.range n, if e i=e n then f i else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have h := hm i n (Finset.mem_range.mp hi) (Nat.lt_succ_self n)
          simp [ne_of_lt h]
        rw [sparseSum, Finset.sum_range_succ]
        change ((sparseSum n r e f + f n*r^(e n))/r^(e n))%r = _
        rw [Nat.add_mul_div_right _ _ (hpos (e n)), Nat.div_eq_of_lt hp, zero_add,
          Nat.mod_eq_of_lt (hf n (Nat.lt_succ_self n)), Finset.sum_range_succ]
        simp [hz]
      · have ht : ∀ i, i<n+1 → e i<k := by
          intro i hi
          by_cases hin : i=n
          · subst i; exact hk
          · exact (hm i n (by omega) (Nat.lt_succ_self n)).trans hk
        have hb := sparseNumberBound (n+1) r k e f hr hm hf ht
        rw [Nat.div_eq_of_lt hb, Nat.zero_mod]
        symm
        apply Finset.sum_eq_zero
        intro i hi
        simp [ne_of_lt (ht i (Finset.mem_range.mp hi))]

theorem sparseDigitExtraction : SparseDigitExtraction := by
  intro n r e f hr hm hf i hi
  rw [sparseAllDigitExtraction n r e f hr hm hf (e i)]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have hne : e j≠e i := by
      intro he
      rcases lt_or_gt_of_ne hji with hlt | hgt
      · have h := hm j i hlt hi
        omega
      · have h := hm i j hgt (Finset.mem_range.mp hj)
        omega
    simp [hne]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr hi))

private theorem capacity_le_base (q : Nat) : 2^q ≤ base q :=
  Nat.pow_le_pow_right Nat.zero_lt_two (by omega)

private theorem base_ge_two (n q : Nat) (hq : n+1<q) : 2≤base q := by
  have h : 2^1 ≤ 2^(4*q) := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  simpa [base] using h

private theorem exponent_strict (i j : Nat) (hij : i<j) : 2^(i+1)<2^(j+1) :=
  Nat.pow_lt_pow_right (by decide : 1<2) (by omega)

theorem cipherDigitExtraction : CipherDigitExtraction := by
  intro n q f hq hf i hi
  exact sparseDigitExtraction n (base q) (fun j => 2^(j+1)) f (base_ge_two n q hq)
    (fun i j hij _ => exponent_strict i j hij)
    (fun j hj => (hf j hj).trans_le (capacity_le_base q)) i hi

theorem cipherInjectivity : CipherInjectivity := by
  intro n q f g hq hf hg
  constructor
  · intro h i hi
    have h1 := cipherDigitExtraction n q f hq hf i hi
    have h2 := cipherDigitExtraction n q g hq hg i hi
    rw [h] at h1
    exact h1.symm.trans h2
  · intro h
    unfold encode
    apply Finset.sum_congr rfl
    intro i hi
    rw [h i (Finset.mem_range.mp hi)]

theorem cipherAddition : CipherAddition := by
  intro n q a b c hq ha hb hc
  have hr := base_ge_two n q hq
  have hm : ∀ i j, i<j → j<n → 2^(i+1)<2^(j+1) :=
    fun i j hij _ => exponent_strict i j hij
  have hsum : ∀ i, i<n → b i+c i<base q := by
    intro i hi
    have hbi := hb i hi
    have hci := hc i hi
    have hp : 2*(2^q) ≤ base q := by
      calc
        _ = 2^(q+1) := by rw [Nat.pow_succ]; ring
        _ ≤ base q := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
    exact lt_of_lt_of_le (by omega : b i+c i<2*(2^q)) hp
  have hlin : sparseSum n (base q) (fun i => 2^(i+1)) (fun i => b i+c i) =
      encode n q b + encode n q c := by
    simp [sparseSum, encode, Nat.add_mul, Finset.sum_add_distrib]
  constructor
  · intro h i hi
    have hw : encode n q a =
        sparseSum n (base q) (fun i => 2^(i+1)) (fun i => b i+c i) := h.trans hlin.symm
    have hd1 := cipherDigitExtraction n q a hq ha i hi
    have hd2 := sparseDigitExtraction n (base q) (fun i => 2^(i+1))
      (fun i => b i+c i) hr hm hsum i hi
    rw [hw] at hd1
    exact hd1.symm.trans hd2
  · intro h
    calc
      encode n q a = sparseSum n (base q) (fun i => 2^(i+1)) (fun i => b i+c i) := by
        unfold encode sparseSum
        apply Finset.sum_congr rfl
        intro i hi
        rw [h i (Finset.mem_range.mp hi)]
      _ = _ := hlin

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherArithmeticProof
