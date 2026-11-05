module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherOnesTargets
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherValidityProof
public import Mathlib.Algebra.Ring.GeomSum

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherOnesForwardProof
open Cipher CipherTargets CipherOnesTargets CipherArithmeticProof CipherValidityProof
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

private theorem sorted_power_sum_injective (i j a b : Nat) (hij : i≤j) (hab : a≤b)
    (h : 2^(i+1)+2^(j+1)=2^(a+1)+2^(b+1)) : i=a ∧ j=b := by
  have hjb : j=b := by
    rcases lt_trichotomy j b with hjb | hjb | hjb
    · have hi : 2^(i+1)≤2^(j+1) := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
      have hupper : 2^(j+1)+2^(j+1)≤2^(b+1) := by
        have hp : 2^(j+2)≤2^(b+1) := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
        rw [show j+2=(j+1)+1 by omega, Nat.pow_succ] at hp
        omega
      have hpos := Nat.two_pow_pos (a+1)
      omega
    · exact hjb
    · have ha : 2^(a+1)≤2^(b+1) := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
      have hupper : 2^(b+1)+2^(b+1)≤2^(j+1) := by
        have hp : 2^(b+2)≤2^(j+1) := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
        rw [show b+2=(b+1)+1 by omega, Nat.pow_succ] at hp
        omega
      have hpos := Nat.two_pow_pos (i+1)
      omega
  have he : 2^(i+1)=2^(a+1) := by rw [hjb] at h; omega
  have hi := Nat.pow_right_injective (by decide : 2≤2) he
  exact ⟨by omega, hjb⟩

private theorem power_sum_eq_iff (i j a b : Nat) :
    2^(i+1)+2^(j+1)=2^(a+1)+2^(b+1) ↔
      (i=a ∧ j=b) ∨ (i=b ∧ j=a) := by
  constructor
  · intro h
    rcases le_total i j with hij | hji <;> rcases le_total a b with hab | hba
    · exact Or.inl (sorted_power_sum_injective i j a b hij hab h)
    · exact Or.inr (sorted_power_sum_injective i j b a hij hba (by simpa [Nat.add_comm] using h))
    · have he := sorted_power_sum_injective j i a b hji hab (by simpa [Nat.add_comm] using h)
      exact Or.inr ⟨he.2, he.1⟩
    · have he := sorted_power_sum_injective j i b a hji hba (by simpa [Nat.add_comm] using h)
      exact Or.inl ⟨he.2, he.1⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> omega

private theorem coefficient_pair (n a b : Nat) (ha : a<n) (hb : b<n) :
    coefficient n (fun _ => 1) (fun _ => 1) (2^(a+1)+2^(b+1)) =
      if a=b then 1 else 2 := by
  by_cases hab : a=b
  · subst b
    simp [coefficient, power_sum_eq_iff, ite_and, ha]
  · have hi (i j : Nat) :
        (if 2^(i+1)+2^(j+1)=2^(a+1)+2^(b+1) then (1:Nat) else 0) =
        (if i=a then (if j=b then 1 else 0) else 0) +
        (if i=b then (if j=a then 1 else 0) else 0) := by
      simp only [power_sum_eq_iff]
      by_cases hia : i=a <;> by_cases hib : i=b <;>
        by_cases hja : j=a <;> by_cases hjb : j=b <;> simp_all
    simp only [coefficient, Nat.mul_one, hi, Finset.sum_add_distrib]
    simp [ha, hb, hab]

private theorem coefficient_zero (n k : Nat)
    (h : ¬ ∃ i j, i<n ∧ j<n ∧ 2^(i+1)+2^(j+1)=k) :
    coefficient n (fun _ => 1) (fun _ => 1) k=0 := by
  unfold coefficient
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  have he : 2^(i+1)+2^(j+1)≠k := fun he => h ⟨i,j,Finset.mem_range.mp hi,Finset.mem_range.mp hj,he⟩
  simp [he]

private theorem coefficient_cases (n k : Nat) :
    coefficient n (fun _ => 1) (fun _ => 1) k=0 ∨
    coefficient n (fun _ => 1) (fun _ => 1) k=1 ∨
    coefficient n (fun _ => 1) (fun _ => 1) k=2 := by
  by_cases h : ∃ i j, i<n ∧ j<n ∧ 2^(i+1)+2^(j+1)=k
  · obtain ⟨i,j,hi,hj,rfl⟩ := h
    rw [coefficient_pair n i j hi hj]
    split_ifs <;> omega
  · exact Or.inl (coefficient_zero n k h)

private theorem doubled_exponent (i : Nat) : 2^(i+1)+2^(i+1)=2^(i+2) := by
  rw [show i+2=(i+1)+1 by omega, Nat.pow_succ]
  omega

private theorem coefficient_one_iff (n k : Nat) :
    coefficient n (fun _ => 1) (fun _ => 1) k=1 ↔ ∃ i, i<n ∧ 2^(i+2)=k := by
  constructor
  · intro hc
    by_cases h : ∃ i j, i<n ∧ j<n ∧ 2^(i+1)+2^(j+1)=k
    · obtain ⟨i,j,hi,hj,rfl⟩ := h
      rw [coefficient_pair n i j hi hj] at hc
      have he : i=j := by split_ifs at hc <;> omega
      subst j
      exact ⟨i,hi,(doubled_exponent i).symm⟩
    · rw [coefficient_zero n k h] at hc
      omega
  · rintro ⟨i,hi,rfl⟩
    rw [← doubled_exponent, coefficient_pair n i i hi hi]
    simp

private theorem base_gt_two (n q : Nat) (hq : n+1<q) : 2<base q := by
  have h : 2^2 ≤ 2^(4*q) := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  change 2<2^(4*q)
  norm_num at h
  omega

private theorem dense_digit (N q : Nat) (f : Nat → Nat) (hq : 0<q)
    (hf : ∀ i, i<N → f i<base q) (k : Nat) :
    (sparseSum N (base q) id f / (base q)^k)%base q = if k<N then f k else 0 := by
  have hr : 2≤base q := by
    have h : 2^1≤2^(4*q) := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
    simpa [base] using h
  rw [sparseAllDigitExtraction N (base q) id f hr (fun _ _ hij _ => hij) hf k]
  simp only [id_eq]
  by_cases hk : k<N
  · rw [if_pos hk, Finset.sum_eq_single k]
    · simp
    · intro j hj hjk
      simp [hjk]
    · intro hkn
      exact False.elim (hkn (Finset.mem_range.mpr hk))
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro j hj
    have hjk : j≠k := by have hj' := Finset.mem_range.mp hj; omega
    simp [hjk]

private theorem dense_and (N q c : Nat) (f : Nat → Nat) (hq : 0<q)
    (hf : ∀ i, i<N → f i<base q) (hc : c<base q) :
    sparseSum N (base q) id f &&& sparseSum N (base q) id (fun _ => c) =
      sparseSum N (base q) id (fun k => f k &&& c) := by
  apply radixExt q _ _ hq
  intro k
  rw [digitAnd, dense_digit N q f hq hf, dense_digit N q (fun _ => c) hq (fun _ _ => hc),
    dense_digit N q (fun k => f k &&& c) hq (fun k hk => lt_of_le_of_lt Nat.and_le_left (hf k hk))]
  split_ifs <;> simp

private theorem low_mask_sum (n q : Nat) (hq : n+1<q) :
    sparseSum (degreeCount n) (base q) id
      (fun k => coefficient n (fun _ => 1) (fun _ => 1) k &&& 1) = shiftedOnes n q := by
  have hr := base_gt_two n q hq
  have hq0 : 0<q := by omega
  have hf : ∀ k, k<degreeCount n → coefficient n (fun _ => 1) (fun _ => 1) k &&& 1 < base q := by
    intro k hk
    exact lt_of_le_of_lt Nat.and_le_right (by omega)
  apply radixExt q _ _ hq0
  intro k
  rw [dense_digit _ q _ hq0 hf]
  change (if k<degreeCount n then _ else 0) =
    (sparseSum n (base q) (fun i => 2^(i+2)) (fun _ => 1)/(base q)^k)%base q
  rw [sparseAllDigitExtraction n (base q) (fun i => 2^(i+2)) (fun _ => 1) (by omega)
    (fun i j hij _ => Nat.pow_lt_pow_right (by decide : 1<2) (by omega)) (fun _ _ => by omega)]
  by_cases h : ∃ i, i<n ∧ 2^(i+2)=k
  · obtain ⟨i,hi,rfl⟩ := h
    have hc := (coefficient_one_iff n (2^(i+2))).2 ⟨i,hi,rfl⟩
    have hd : 2^(i+2)<degreeCount n := by simpa only [doubled_exponent] using degree_lt n i i hi hi
    rw [if_pos hd, hc]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      have he : 2^(j+2)≠2^(i+2) := by
        intro he
        have hi' := Nat.pow_right_injective (by decide : 2≤2) he
        omega
      simp [he]
    · intro hi'
      exact False.elim (hi' (Finset.mem_range.mpr hi))
  · have hs : (∑ i ∈ Finset.range n, if 2^(i+2)=k then (1:Nat) else 0)=0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have he : 2^(i+2)≠k := fun he => h ⟨i,Finset.mem_range.mp hi,he⟩
      simp [he]
    rw [hs]
    have hc : coefficient n (fun _ => 1) (fun _ => 1) k≠1 := by
      intro hc
      exact h ((coefficient_one_iff n k).1 hc)
    rcases coefficient_cases n k with he | he | he <;> simp_all

private theorem ones_shift (n q : Nat) :
    (base q)^2+shiftedOnes n q = ones n q+(base q)^(2^(n+1)) := by
  induction n with
  | zero => simp [ones, shiftedOnes, encode, shiftedEncode]
  | succ n ih =>
      simp only [ones, shiftedOnes, encode, shiftedEncode, Finset.sum_range_succ, Nat.one_mul] at ih ⊢
      have he : n+1+1=n+2 := by omega
      rw [he]
      omega

private theorem shifted_divisible (n q : Nat) : (base q)^4 ∣ shiftedOnes n q := by
  unfold shiftedOnes shiftedEncode
  apply Finset.dvd_sum
  intro i hi
  simp only [Nat.one_mul]
  apply pow_dvd_pow
  have h : 2^2≤2^(i+2) := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  norm_num at h
  exact h

theorem onesEquationsForward : OnesEquationsForward := by
  intro n q hq
  refine ⟨hq, ?_⟩
  by_cases hn : n=0
  · left
    simp [hn, ones, shiftedOnes, encode, shiftedEncode]
  · right
    have hn0 : 0<n := by omega
    have hq0 : 0<q := by omega
    have hr := base_gt_two n q hq
    let C := coefficient n (fun _ => 1) (fun _ => 1)
    let W := sparseSum (degreeCount n) (base q) id (fun _ => 1)
    let U2 := sparseSum (degreeCount n) (base q) id (fun k => C k &&& 2)
    have hC : ∀ k, k<degreeCount n → C k<base q := by
      intro k hk
      rcases coefficient_cases n k with he | he | he <;> dsimp [C] <;> omega
    have hsq : ones n q*ones n q=sparseSum (degreeCount n) (base q) id C := by
      exact product_expansion n q (fun _ => 1) (fun _ => 1)
    have hlow : sparseSum (degreeCount n) (base q) id (fun k => C k &&& 1)=shiftedOnes n q :=
      low_mask_sum n q hq
    have hW : 1+(base q-1)*W=base q*(base q)^(2^(n+1)) := by
      have hg := geom_sum_mul_add (base q-1) (degreeCount n)
      have hb : base q-1+1=base q := by omega
      rw [hb] at hg
      dsimp [W, sparseSum, degreeCount]
      simp only [Nat.one_mul, id_eq]
      unfold degreeCount at hg
      rw [Nat.pow_succ (base q) (2^(n+1))] at hg
      simpa [Nat.add_comm, Nat.mul_comm] using hg
    have hW2 : 2*W=sparseSum (degreeCount n) (base q) id (fun _ => 2) := by
      simp [W, sparseSum, Finset.mul_sum]
    refine ⟨hn0,W,U2,hW,?_,?_,?_,ones_shift n q,shifted_divisible n q⟩
    · rw [hsq, ← hlow]
      dsimp [U2]
      simp only [sparseSum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      have he : C k=(C k &&& 1)+(C k &&& 2) := by
        rcases coefficient_cases n k with he | he | he <;> dsimp [C] <;> rw [he] <;> decide
      simpa only [Nat.add_mul] using congrArg (fun t : Nat => t*(base q)^(id k)) he
    · rw [hsq, dense_and _ q 1 C hq0 hC (by omega)]
      exact hlow.symm
    · rw [hsq, hW2, dense_and _ q 2 C hq0 hC hr]

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherOnesForwardProof
