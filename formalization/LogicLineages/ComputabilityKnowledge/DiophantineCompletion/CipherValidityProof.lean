module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherArithmeticProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherValidityProof
open Cipher CipherTargets CipherArithmeticProof
open scoped BigOperators

theorem digitAnd (q k a b : Nat) :
    ((a &&& b)/(base q)^k)%base q =
      ((a/(base q)^k)%base q) &&& ((b/(base q)^k)%base q) := by
  unfold base
  rw [← Nat.pow_mul, Nat.and_div_two_pow, Nat.and_mod_two_pow]

theorem radixExt (q a b : Nat) (hq : 0<q)
    (h : ∀ k, (a/(base q)^k)%base q = (b/(base q)^k)%base q) : a=b := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hw : 0<4*q := by omega
  have hj := Nat.mod_lt i hw
  have hd := congrArg (fun d => d.testBit (i%(4*q))) (h (i/(4*q)))
  simpa [base, ← Nat.pow_mul, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    hj, Nat.mod_add_div] using hd

private theorem base_ge_two (n q : Nat) (hq : n+1<q) : 2≤base q := by
  have h : 2^1 ≤ 2^(4*q) := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  simpa [base] using h

private theorem capacity_le_base (q : Nat) : 2^q ≤ base q :=
  Nat.pow_le_pow_right Nat.zero_lt_two (by omega)

private theorem exponent_strict (i j : Nat) (hij : i<j) : 2^(i+1)<2^(j+1) :=
  Nat.pow_lt_pow_right (by decide : 1<2) (by omega)

private theorem absentDigit (n r : Nat) (e f : Nat → Nat) (hr : 2≤r)
    (hm : ∀ i j, i<j → j<n → e i<e j) (hf : ∀ i, i<n → f i<r)
    (k : Nat) (hk : ¬ ∃ i, i<n ∧ e i=k) :
    (sparseSum n r e f / r^k)%r = 0 := by
  rw [sparseAllDigitExtraction n r e f hr hm hf k]
  apply Finset.sum_eq_zero
  intro i hi
  have hne : e i≠k := by
    intro h
    exact hk ⟨i, Finset.mem_range.mp hi, h⟩
  simp [hne]

theorem cipherValidityCharacterization : CipherValidityCharacterization := by
  intro n q a
  have hm : ∀ i j, i<j → j<n → 2^(i+1)<2^(j+1) :=
    fun i j hij _ => exponent_strict i j hij
  have hp : 2^q-1 < base q := by
    have h1 := Nat.two_pow_pos q
    have h2 := capacity_le_base q
    omega
  have hM : (2^q-1)*ones n q =
      sparseSum n (base q) (fun i => 2^(i+1)) (fun _ => 2^q-1) := by
    simp [ones, encode, sparseSum, Finset.mul_sum]
  constructor
  · rintro ⟨f, hq, hf, rfl⟩
    have hr := base_ge_two n q hq
    have hfr : ∀ i, i<n → f i<base q :=
      fun i hi => (hf i hi).trans_le (capacity_le_base q)
    refine ⟨hq, ?_⟩
    apply radixExt q _ _ (by omega)
    intro k
    rw [digitAnd]
    by_cases hk : ∃ i, i<n ∧ 2^(i+1)=k
    · obtain ⟨i, hi, rfl⟩ := hk
      rw [cipherDigitExtraction n q f hq hf i hi, hM,
        sparseDigitExtraction n (base q) (fun i => 2^(i+1))
          (fun _ => 2^q-1) hr hm (fun _ _ => hp) i hi]
      exact Nat.and_two_pow_sub_one_of_lt_two_pow (hf i hi)
    · have hz := absentDigit n (base q) (fun i => 2^(i+1)) f hr hm hfr k hk
      change (encode n q f/(base q)^k)%base q=0 at hz
      simp [hz]
  · rintro ⟨hq, hmask⟩
    have hr := base_ge_two n q hq
    let f : Nat → Nat := fun i => (a/(base q)^(2^(i+1)))%base q
    have hf : Bounded n q f := by
      intro i hi
      have hd := congrArg (fun d => (d/(base q)^(2^(i+1)))%base q) hmask
      rw [digitAnd, hM,
        sparseDigitExtraction n (base q) (fun i => 2^(i+1))
          (fun _ => 2^q-1) hr hm (fun _ _ => hp) i hi] at hd
      change f i &&& (2^q-1)=f i at hd
      have hle : f i≤2^q-1 :=
        calc f i = f i &&& (2^q-1) := hd.symm
             _ ≤ _ := Nat.and_le_right
      have hpos := Nat.two_pow_pos q
      omega
    have hfr : ∀ i, i<n → f i<base q :=
      fun i hi => (hf i hi).trans_le (capacity_le_base q)
    have he : a=encode n q f := by
      apply radixExt q _ _ (by omega)
      intro k
      by_cases hk : ∃ i, i<n ∧ 2^(i+1)=k
      · obtain ⟨i, hi, rfl⟩ := hk
        exact (cipherDigitExtraction n q f hq hf i hi).symm
      · have hmz := absentDigit n (base q) (fun i => 2^(i+1))
          (fun _ => 2^q-1) hr hm (fun _ _ => hp) k hk
        have had := congrArg (fun d => (d/(base q)^k)%base q) hmask
        rw [digitAnd, hM, hmz] at had
        have haz : (a/(base q)^k)%base q=0 := by simpa using had.symm
        have hez := absentDigit n (base q) (fun i => 2^(i+1)) f hr hm hfr k hk
        change (encode n q f/(base q)^k)%base q=0 at hez
        exact haz.trans hez.symm
    exact ⟨f, hq, hf, he⟩

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherValidityProof
