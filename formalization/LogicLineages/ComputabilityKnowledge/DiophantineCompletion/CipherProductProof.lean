module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherValidityProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherProductProof
open Cipher CipherTargets CipherArithmeticProof CipherValidityProof
open scoped BigOperators

private def coefficient (n : Nat) (b c : Nat → Nat) (k : Nat) : Nat :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
    if 2^(i+1)+2^(j+1)=k then b i*c j else 0

private def degreeCount (n : Nat) : Nat := 2^(n+1)+1

private theorem degree_lt (n i j : Nat) (hi : i<n) (hj : j<n) :
    2^(i+1)+2^(j+1)<degreeCount n := by
  have h1 : 2^(i+1)≤2^n := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  have h2 : 2^(j+1)≤2^n := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  unfold degreeCount
  rw [Nat.pow_succ]
  omega

private theorem sum_ne_power (i j k : Nat) (hij : i<j) : 2^i+2^j≠2^k := by
  intro h
  have hpos := Nat.two_pow_pos i
  have hlt : 2^i<2^j := Nat.pow_lt_pow_right (by decide : 1<2) hij
  have hlo : 2^j<2^i+2^j := by omega
  have hhi : 2^i+2^j<2^(j+1) := by rw [Nat.pow_succ]; omega
  by_cases hk : k≤j
  · have hp : 2^k≤2^j := Nat.pow_le_pow_right Nat.zero_lt_two hk
    omega
  · have hp : 2^(j+1)≤2^k := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
    omega

private theorem power_sum_diagonal (i j k : Nat)
    (h : 2^(i+1)+2^(j+1)=2^(k+2)) : i=k ∧ j=k := by
  have hij : i=j := by
    rcases lt_trichotomy i j with hij | hij | hij
    · exact False.elim (sum_ne_power (i+1) (j+1) (k+2) (by omega) h)
    · exact hij
    · apply False.elim
      apply sum_ne_power (j+1) (i+1) (k+2) (by omega)
      simpa [Nat.add_comm] using h
  subst j
  have hd : 2^(i+1)+2^(i+1)=2^(i+2) := by
    rw [show i+2=(i+1)+1 by omega, Nat.pow_succ]
    omega
  have hp : 2^(i+2)=2^(k+2) := hd.symm.trans h
  have hik : i=k := by
    rcases lt_trichotomy i k with hik | hik | hik
    · have hlt : 2^(i+2)<2^(k+2) := Nat.pow_lt_pow_right (by decide : 1<2) (by omega)
      omega
    · exact hik
    · have hlt : 2^(k+2)<2^(i+2) := Nat.pow_lt_pow_right (by decide : 1<2) (by omega)
      omega
  exact ⟨hik, hik⟩

private theorem diagonal_coefficient (n : Nat) (b c : Nat → Nat) (i : Nat) (hi : i<n) :
    coefficient n b c (2^(i+2)) = b i*c i := by
  unfold coefficient
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i]
    · have hd : 2^(i+1)+2^(i+1)=2^(i+2) := by
        rw [show i+2=(i+1)+1 by omega, Nat.pow_succ]
        omega
      simp [hd]
    · intro j hj hji
      have hn : 2^(i+1)+2^(j+1)≠2^(i+2) := by
        intro h
        exact hji (power_sum_diagonal i j i h).2
      simp [hn]
    · intro h
      exact False.elim (h (Finset.mem_range.mpr hi))
  · intro j hj hji
    apply Finset.sum_eq_zero
    intro k hk
    have hn : 2^(j+1)+2^(k+1)≠2^(i+2) := by
      intro h
      exact hji (power_sum_diagonal j k i h).1
    simp [hn]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr hi))

private theorem coefficient_bound (n q : Nat) (b c : Nat → Nat)
    (hq : n+1<q) (hb : Bounded n q b) (hc : Bounded n q c) (k : Nat) :
    coefficient n b c k < base q := by
  let B := 2^q
  have hB : 0<B := Nat.two_pow_pos q
  have hn : n≤B := by
    have h : q<2^q := Nat.lt_two_pow_self
    dsimp [B]
    omega
  have hs : coefficient n b c k ≤ n*n*(B-1)^2 := by
    unfold coefficient
    calc
      _ ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (B-1)^2 := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        have hbi : b i≤B-1 := by have h := hb i (Finset.mem_range.mp hi); dsimp [B]; omega
        have hcj : c j≤B-1 := by have h := hc j (Finset.mem_range.mp hj); dsimp [B]; omega
        split_ifs
        · simpa [Nat.pow_two] using Nat.mul_le_mul hbi hcj
        · exact Nat.zero_le _
      _ = _ := by simp; ring
  have hn2 : n*n≤B*B := Nat.mul_le_mul hn hn
  have hm2 : (B-1)^2<B^2 :=
    Nat.pow_lt_pow_left (by omega : B-1<B) (by decide : 2≠0)
  calc
    _ ≤ n*n*(B-1)^2 := hs
    _ ≤ (B*B)*(B-1)^2 := Nat.mul_le_mul_right _ hn2
    _ < (B*B)*(B^2) := Nat.mul_lt_mul_of_pos_left hm2 (Nat.mul_pos hB hB)
    _ = B^4 := by ring
    _ = base q := by
      dsimp [B, base]
      rw [← Nat.pow_mul]
      congr 1
      omega

private theorem product_expansion (n q : Nat) (b c : Nat → Nat) :
    encode n q b * encode n q c =
      sparseSum (degreeCount n) (base q) id (coefficient n b c) := by
  let G : Nat → Nat → Nat → Nat := fun i j k =>
    (if 2^(i+1)+2^(j+1)=k then b i*c j else 0)*(base q)^k
  have ht (i : Nat) (hi : i<n) (j : Nat) (hj : j<n) :
      b i*c j*(base q)^(2^(i+1)+2^(j+1)) = ∑ k ∈ Finset.range (degreeCount n), G i j k := by
    symm
    rw [Finset.sum_eq_single (2^(i+1)+2^(j+1))]
    · simp [G]
    · intro k hk hne
      simp [G, Ne.symm hne]
    · intro h
      exact False.elim (h (Finset.mem_range.mpr (degree_lt n i j hi hj)))
  have hd : sparseSum (degreeCount n) (base q) id (coefficient n b c) =
      ∑ k ∈ Finset.range (degreeCount n), ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, G i j k := by
    simp only [sparseSum, coefficient, id_eq, Finset.sum_mul, G]
  calc
    _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        b i*c j*(base q)^(2^(i+1)+2^(j+1)) := by
      unfold encode
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Nat.pow_add]
      ring
    _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        ∑ k ∈ Finset.range (degreeCount n), G i j k := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact ht i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
    _ = ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range (degreeCount n),
        ∑ j ∈ Finset.range n, G i j k := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.range (degreeCount n), ∑ i ∈ Finset.range n,
        ∑ j ∈ Finset.range n, G i j k := by rw [Finset.sum_comm]
    _ = _ := hd.symm

private theorem base_ge_two (n q : Nat) (hq : n+1<q) : 2≤base q := by
  have h : 2^1 ≤ 2^(4*q) := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  simpa [base] using h

private theorem shifted_exponent_strict (i j : Nat) (hij : i<j) : 2^(i+2)<2^(j+2) :=
  Nat.pow_lt_pow_right (by decide : 1<2) (by omega)

private theorem shifted_absent (n q : Nat) (f : Nat → Nat)
    (hr : 2≤base q) (hf : ∀ i, i<n → f i<base q)
    (k : Nat) (hk : ¬ ∃ i, i<n ∧ 2^(i+2)=k) :
    (shiftedEncode n q f/(base q)^k)%base q=0 := by
  rw [show shiftedEncode n q f = sparseSum n (base q) (fun i => 2^(i+2)) f from rfl,
    sparseAllDigitExtraction n (base q) (fun i => 2^(i+2)) f hr
      (fun i j hij _ => shifted_exponent_strict i j hij) hf k]
  apply Finset.sum_eq_zero
  intro i hi
  have hn : 2^(i+2)≠k := fun h => hk ⟨i, Finset.mem_range.mp hi, h⟩
  simp [hn]

theorem cipherProductMask : CipherProductMask := by
  intro n q b c hq hb hc
  have hr := base_ge_two n q hq
  have hm : ∀ i j, i<j → j<n → 2^(i+2)<2^(j+2) :=
    fun i j hij _ => shifted_exponent_strict i j hij
  have hprod : ∀ i, i<n → b i*c i<base q := by
    intro i hi
    rw [← diagonal_coefficient n b c i hi]
    exact coefficient_bound n q b c hq hb hc _
  have hM : (base q-1)*shiftedOnes n q =
      shiftedEncode n q (fun _ => base q-1) := by
    simp [shiftedOnes, shiftedEncode, Finset.mul_sum]
  have hmask : ∀ i, i<n → base q-1<base q := by intro i hi; omega
  apply radixExt q _ _ (by omega)
  intro k
  rw [digitAnd]
  by_cases hk : ∃ i, i<n ∧ 2^(i+2)=k
  · obtain ⟨i, hi, rfl⟩ := hk
    have hdeg : 2^(i+2)<degreeCount n := by
      have h := degree_lt n i i hi hi
      have he : 2^(i+1)+2^(i+1)=2^(i+2) := by
        rw [show i+2=(i+1)+1 by omega, Nat.pow_succ]
        omega
      rwa [he] at h
    have hd : (encode n q b*encode n q c/(base q)^(2^(i+2)))%base q = b i*c i := by
      rw [product_expansion n q b c]
      have he := sparseDigitExtraction (degreeCount n) (base q) id (coefficient n b c) hr
          (fun _ _ hij _ => hij) (fun j _ => coefficient_bound n q b c hq hb hc j)
          (2^(i+2)) hdeg
      simpa only [id_eq, diagonal_coefficient n b c i hi] using he
    have hmD := sparseDigitExtraction n (base q) (fun i => 2^(i+2))
      (fun _ => base q-1) hr hm hmask i hi
    have hpD := sparseDigitExtraction n (base q) (fun i => 2^(i+2))
      (fun i => b i*c i) hr hm hprod i hi
    change (shiftedEncode n q (fun _ => base q-1)/(base q)^(2^(i+2)))%base q=base q-1 at hmD
    change (shiftedEncode n q (fun i => b i*c i)/(base q)^(2^(i+2)))%base q=b i*c i at hpD
    rw [hd, hM, hmD, hpD]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (hprod i hi)
  · have hm0 := shifted_absent n q (fun _ => base q-1) hr hmask k hk
    have hp0 := shifted_absent n q (fun i => b i*c i) hr hprod k hk
    rw [hM, hm0, hp0]
    simp

theorem cipherMultiplication : CipherMultiplication := by
  intro n q a b c hq ha hb hc
  have hr := base_ge_two n q hq
  have hOne : Bounded n q (fun _ => 1) := by
    intro i hi
    exact Nat.pow_lt_pow_right (by decide : 1<2) (by omega : 0<q)
  have hA := cipherProductMask n q a (fun _ => 1) hq ha hOne
  have hBC := cipherProductMask n q b c hq hb hc
  change (encode n q a*ones n q) &&& ((base q-1)*shiftedOnes n q) =
    shiftedEncode n q (fun i => a i*1) at hA
  simp only [Nat.mul_one] at hA
  rw [hA, hBC]
  have hprod : ∀ i, i<n → b i*c i<base q := by
    intro i hi
    rw [← diagonal_coefficient n b c i hi]
    exact coefficient_bound n q b c hq hb hc _
  have hcap : 2^q≤base q := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  constructor
  · intro h i hi
    have h1 := sparseDigitExtraction n (base q) (fun i => 2^(i+2)) a hr
      (fun i j hij _ => shifted_exponent_strict i j hij)
      (fun i hi => (ha i hi).trans_le hcap) i hi
    have h2 := sparseDigitExtraction n (base q) (fun i => 2^(i+2)) (fun i => b i*c i) hr
      (fun i j hij _ => shifted_exponent_strict i j hij) hprod i hi
    change (shiftedEncode n q a/(base q)^(2^(i+2)))%base q=a i at h1
    change (shiftedEncode n q (fun i => b i*c i)/(base q)^(2^(i+2)))%base q=b i*c i at h2
    rw [h] at h1
    exact h1.symm.trans h2
  · intro h
    unfold shiftedEncode
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun t : Nat => t*(base q)^(2^(i+2)))
      (h i (Finset.mem_range.mp hi))

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherProductProof
