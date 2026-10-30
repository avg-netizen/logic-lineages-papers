module
public import LogicLineages.OrdinalComparison.SparseSignedOrientationTargets
public import LogicLineages.OrdinalComparison.SparseSignedNumericalProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

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

theorem sparseSignedNumericalOrientation : Targets.SparseSignedNumericalOrientation := by
  intro row p q x hn hv hp hx
  rcases choose_sparse_max row hn hp with ⟨entry,rest,hperm,hmax⟩
  have he : entry∈row := hperm.mem_iff.mpr List.mem_cons_self
  have hd := hv entry he
  have hrest : ∀ other∈rest, other∈row := by
    intro other hm
    exact hperm.mem_iff.mpr (List.mem_cons_of_mem entry hm)
  let U := Phi (entry.2.2-1)
  let C := (rest.map (fun other => other.1.natAbs)).sum
  let K := 2*(row.map (fun other => other.1.natAbs)).sum+p.natAbs+q.natAbs
  have hfour : 4≤x := (le_max_left _ _).trans hx
  have hKx : K≤x := (le_max_right _ _).trans hx
  have hs : 0<entry.2.2 := by omega
  have hxU : x≤U := by
    have h := self_lt_Phi (entry.2.2-1)
    dsimp only [U]
    omega
  have hU : 1≤U := by have h := four_le_Phi (entry.2.2-1); dsimp only [U]; omega
  have hgap : K*U<Phi entry.2.2 := phiPreviousProductGap entry.2.2 K hs (hKx.trans hd.2.1)
  have hvals : ∀ other∈rest, other.2.1≤2*U := by
    intro other hm
    have ho := hv other (hrest other hm)
    have hm' := hmax other hm
    have hindex : other.2.2≤entry.2.2-1 := by omega
    exact ho.2.2.2.le.trans (Nat.mul_le_mul_left 2 (Phi_strictMono.monotone hindex))
  have hsum := (hperm.map (fun other => other.1.natAbs)).sum_eq
  simp only [List.map_cons,List.sum_cons] at hsum
  have hK : K=2*(entry.1.natAbs+C)+p.natAbs+q.natAbs := by
    dsimp only [K,C]
    rw [hsum]
  let lower : Int := (rest.map (fun other => other.1*(other.2.1 : Int))).sum+p*(x : Int)+q
  have hlower : lower.natAbs≤K*U := by
    have hr := weighted_abs_bound rest U hvals
    have h1 := Int.natAbs_add_le ((rest.map (fun other => other.1*(other.2.1 : Int))).sum) (p*(x : Int))
    have h2 := Int.natAbs_add_le ((rest.map (fun other => other.1*(other.2.1 : Int))).sum+p*(x : Int)) q
    simp only [Int.natAbs_mul,Int.natAbs_natCast] at h1
    have hpx := Nat.mul_le_mul_left p.natAbs hxU
    have hq := Nat.mul_le_mul_left q.natAbs hU
    have hfirst : lower.natAbs≤2*U*C+p.natAbs*x+q.natAbs := by
      dsimp only [lower,C]
      omega
    have hcoefbound : 2*C+p.natAbs+q.natAbs≤K := by
      rw [hK]
      omega
    calc
      lower.natAbs≤2*U*C+p.natAbs*x+q.natAbs := hfirst
      _≤2*U*C+p.natAbs*U+q.natAbs*U := by omega
      _=(2*C+p.natAbs+q.natAbs)*U := by ring
      _≤K*U := Nat.mul_le_mul_right U hcoefbound
  have hcoef : 1≤entry.1.natAbs := Int.natAbs_pos.mpr hd.1
  have hleading : K*U<(entry.1*(entry.2.1 : Int)).natAbs := by
    simp only [Int.natAbs_mul,Int.natAbs_natCast]
    have hh : entry.2.1≤entry.1.natAbs*entry.2.1 := by nlinarith
    exact (hgap.trans hd.2.2.1).trans_le hh
  intro chosen hchosen hchosenmax
  have hchosenEq : chosen=entry := by
    rcases List.mem_cons.mp (hperm.mem_iff.mp hchosen) with heq | hm
    · exact heq
    · have hlt := hmax chosen hm
      have hle := hchosenmax entry he
      omega
  subst chosen
  have hnat : lower.natAbs<(entry.1*(entry.2.1 : Int)).natAbs := hlower.trans_lt hleading
  have habs : |lower| < |entry.1*(entry.2.1 : Int)| := by
    have hcast : (lower.natAbs : Int)<((entry.1*(entry.2.1 : Int)).natAbs : Int) := by exact_mod_cast hnat
    simpa only [Int.natCast_natAbs] using hcast
  have hvpos : 0<(entry.2.1 : Int) := by
    have hfourPhi := four_le_Phi entry.2.2
    have hvNat : 0<entry.2.1 := by omega
    exact_mod_cast hvNat
  have hvsum := (hperm.map (fun other => other.1*(other.2.1 : Int))).sum_eq
  have heq : (row.map (fun other => other.1*(other.2.1 : Int))).sum+p*(x : Int)+q=
      entry.1*(entry.2.1 : Int)+lower := by
    rw [hvsum]
    simp only [List.map_cons,List.sum_cons]
    dsimp only [lower]
    ring
  rw [heq]
  by_cases hc : 0<entry.1
  · have hm := mul_pos hc hvpos
    rw [abs_of_pos hm] at habs
    have hl := neg_abs_le lower
    have hpos : 0<entry.1*(entry.2.1 : Int)+lower := by linarith
    rw [Int.sign_eq_one_of_pos hpos,Int.sign_eq_one_of_pos hc]
  · have hcneg : entry.1<0 := by have hne := hd.1; omega
    have hm := mul_neg_of_neg_of_pos hcneg hvpos
    rw [abs_of_neg hm] at habs
    have hl := le_abs_self lower
    have hneg : entry.1*(entry.2.1 : Int)+lower<0 := by linarith
    rw [Int.sign_eq_neg_one_of_neg hneg,Int.sign_eq_neg_one_of_neg hcneg]

end LogicLineages.OrdinalComparison
