module
public import LogicLineages.OrdinalComparison.CommonHeadLargeRowTargets
public import LogicLineages.OrdinalComparison.SparseSignedNumericalProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.CommonHeadLargeRow.Proof

private theorem sparse_square_le_power (n : Nat) (hn : 4≤n) : n*n≤2^n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have hp : (n+1)*(n+1)≤2*(n*n) := by nlinarith
    calc
      (n+1)*(n+1)≤2*(n*n) := hp
      _≤2*2^n := Nat.mul_le_mul_left 2 ih
      _=2^(n+1) := by rw [Nat.pow_succ,Nat.mul_comm]

private theorem choose_sparse_max (row : List (Int × Nat × Nat)) (hn : row≠[])
    (hp : row.Pairwise (fun a b => a.2.2≠b.2.2)) :
    ∃ entry rest, row.Perm (entry::rest) ∧ ∀ other∈rest, other.2.2<entry.2.2 := by
  induction row with
  | nil => exact False.elim (hn rfl)
  | cons a tail ih =>
    by_cases ht : tail=[]
    · subst tail
      exact ⟨a,[],List.Perm.refl _,by simp⟩
    rcases ih ht (List.pairwise_cons.mp hp).2 with ⟨b,rest,hperm,hmax⟩
    have hb : b∈tail := hperm.mem_iff.mpr List.mem_cons_self
    have hne := (List.pairwise_cons.mp hp).1 b hb
    by_cases hab : a.2.2<b.2.2
    · refine ⟨b,a::rest,(List.Perm.cons a hperm).trans (List.Perm.swap b a rest),?_⟩
      intro other hm
      rcases List.mem_cons.mp hm with h | h
      · subst other; exact hab
      · exact hmax other h
    · have hba : b.2.2<a.2.2 := by omega
      refine ⟨a,tail,List.Perm.refl _,?_⟩
      intro other hm
      rcases List.mem_cons.mp (hperm.mem_iff.mp hm) with h | h
      · subst other; exact hba
      · exact (hmax other h).trans hba

private theorem weighted_abs_bound (row : List (Int × Nat × Nat)) (U : Nat)
    (hv : ∀ entry∈row, entry.2.1≤2*U) :
    ((row.map (fun entry => entry.1*(entry.2.1 : Int))).sum).natAbs≤
      2*U*(row.map (fun entry => entry.1.natAbs)).sum := by
  induction row with
  | nil => simp
  | cons a rest ih =>
    have ha := hv a List.mem_cons_self
    have hr := ih (fun entry hm => hv entry (List.mem_cons_of_mem a hm))
    have hadd := Int.natAbs_add_le (a.1*(a.2.1 : Int))
      ((rest.map (fun entry => entry.1*(entry.2.1 : Int))).sum)
    simp only [Int.natAbs_mul,Int.natAbs_natCast] at hadd
    simp only [List.map_cons,List.sum_cons]
    have hm := Nat.mul_le_mul_left a.1.natAbs ha
    nlinarith

theorem numericalDominance : Targets.NumericalDominance := by
  intro K row hp hv chosen hchosen hchosen0 hchosenmax
  have hn : row≠[] := by intro h; subst row; simp at hchosen
  obtain ⟨entry,rest,hperm,hmax⟩ := choose_sparse_max row hn hp
  have he : entry∈row := hperm.mem_iff.mpr List.mem_cons_self
  have heq : chosen=entry := by
    rcases List.mem_cons.mp (hperm.mem_iff.mp hchosen) with h | h
    · exact h
    · have hlt := hmax chosen h
      have hle := hchosenmax entry he
      omega
  subst chosen
  have hd := hv entry he
  have hrest : ∀ other∈rest, other∈row := by
    intro other hm
    exact hperm.mem_iff.mpr (List.mem_cons_of_mem entry hm)
  let U := Phi (entry.2.2-1)
  let M := numericalMass row
  let C := (rest.map (fun other => other.1.natAbs)).sum
  have hfour : 4≤entry.2.2 := (le_max_left _ _).trans hd.1
  have hM : 2*M≤entry.2.2 := (le_max_left _ _).trans ((le_max_right _ _).trans hd.1)
  have hK : 4*K.natAbs+4≤entry.2.2 := (le_max_right _ _).trans ((le_max_right _ _).trans hd.1)
  have hs : 0<entry.2.2 := by omega
  have hsU : entry.2.2≤U := by
    have h := self_lt_Phi (entry.2.2-1)
    dsimp only [U]
    omega
  have hU : 4≤U := four_le_Phi _
  have hMU : 2*M≤U := hM.trans hsU
  have hKU : K.natAbs<U := by omega
  have hsum := (hperm.map (fun other => other.1.natAbs)).sum_eq
  simp only [List.map_cons,List.sum_cons] at hsum
  have hMC : M=entry.1.natAbs+C := hsum
  have hcoef : 1≤entry.1.natAbs := Int.natAbs_pos.mpr hchosen0
  have hMpos : 1≤M := by omega
  have hCM : C≤M := by omega
  have hgap : 4*M*U≤Phi entry.2.2 := by
    calc
      4*M*U≤2*(U*U) := by nlinarith
      _≤2*2^U := Nat.mul_le_mul_left 2 (sparse_square_le_power U hU)
      _=2^(U+1) := by rw [Nat.pow_succ,Nat.mul_comm]
      _≤2^(2^(U+1)) := (Nat.lt_two_pow_self).le
      _≤Phi entry.2.2 := by
        simpa only [U,Nat.sub_add_cancel hs] using Phi_succ_gap (entry.2.2-1)
  have hvals : ∀ other∈rest, other.2.1≤2*U := by
    intro other hm
    have ho := hv other (hrest other hm)
    have hm' := hmax other hm
    have hi : other.2.2≤entry.2.2-1 := by omega
    exact ho.2.2.le.trans (Nat.mul_le_mul_left 2 (Phi_strictMono.monotone hi))
  let lower : Int := K+(rest.map (fun other => other.1*(other.2.1:Int))).sum
  have hlower : lower.natAbs<4*M*U := by
    have hr := weighted_abs_bound rest U hvals
    have hadd := Int.natAbs_add_le K ((rest.map (fun other => other.1*(other.2.1:Int))).sum)
    have hbound : lower.natAbs≤K.natAbs+2*U*C := by
      dsimp only [lower,C]
      omega
    have hprod : U*C≤U*M := Nat.mul_le_mul_left U hCM
    have hprodpos : U≤U*M := by nlinarith
    nlinarith
  have hleading : 4*M*U<(entry.1*(entry.2.1:Int)).natAbs := by
    simp only [Int.natAbs_mul,Int.natAbs_natCast]
    have hh : entry.2.1≤entry.1.natAbs*entry.2.1 := by nlinarith
    exact (hgap.trans_lt hd.2.1).trans_le hh
  have habs : |lower| < |entry.1*(entry.2.1:Int)| := by
    have hnat := hlower.trans hleading
    have hcast : (lower.natAbs:Int)<((entry.1*(entry.2.1:Int)).natAbs:Int) := by exact_mod_cast hnat
    simpa only [Int.natCast_natAbs] using hcast
  have hvpos : 0<(entry.2.1:Int) := by
    have h := four_le_Phi entry.2.2
    have hpos : 0<entry.2.1 := by omega
    exact_mod_cast hpos
  have hvsum := (hperm.map (fun other => other.1*(other.2.1:Int))).sum_eq
  have hvalue : numericalValue K row=entry.1*(entry.2.1:Int)+lower := by
    unfold numericalValue
    rw [hvsum]
    simp only [List.map_cons,List.sum_cons]
    dsimp only [lower]
    ring
  rw [hvalue]
  by_cases hc : 0<entry.1
  · have hm := mul_pos hc hvpos
    rw [abs_of_pos hm] at habs
    have hl := neg_abs_le lower
    have hpos : 0<entry.1*(entry.2.1:Int)+lower := by linarith
    rw [Int.sign_eq_one_of_pos hpos,Int.sign_eq_one_of_pos hc]
  · have hcneg : entry.1<0 := by omega
    have hm := mul_neg_of_neg_of_pos hcneg hvpos
    rw [abs_of_neg hm] at habs
    have hl := le_abs_self lower
    have hneg : entry.1*(entry.2.1:Int)+lower<0 := by linarith
    rw [Int.sign_eq_neg_one_of_neg hneg,Int.sign_eq_neg_one_of_neg hcneg]
end LogicLineages.OrdinalComparison.CommonHeadLargeRow.Proof
