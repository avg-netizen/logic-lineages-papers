module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedWindowProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedNumerical.Proof
open CommonHeadLargeRow

/-- The same elementary sparse-band estimate as the checked common-head
supplier, used here with an OPEN remainder rather than a small constant. -/
private theorem square_le_power (n:Nat) (hn:4≤n):n*n≤2^n:=by
  induction n,hn using Nat.le_induction with
  | base=>decide
  | succ n hn ih=>
    have hp:(n+1)*(n+1)≤2*(n*n):=by nlinarith
    calc
      (n+1)*(n+1)≤2*(n*n):=hp
      _≤2*2^n:=Nat.mul_le_mul_left 2 ih
      _=2^(n+1):=by rw [Nat.pow_succ,Nat.mul_comm]

private theorem weighted_abs (row:NumericalRow) (U:Nat)
    (hv:∀a∈row,a.2.1≤2*U):
    ((row.map (fun a=>a.1*(a.2.1:Int))).sum).natAbs≤
      2*U*(row.map (fun a=>a.1.natAbs)).sum:=by
  induction row with
  | nil=>simp
  | cons a row ih=>
    have ha:=hv a List.mem_cons_self
    have hr:=ih (fun b hb=>hv b (List.mem_cons_of_mem a hb))
    have hadd:=Int.natAbs_add_le (a.1*(a.2.1:Int)) ((row.map (fun b=>b.1*(b.2.1:Int))).sum)
    simp only [Int.natAbs_mul,Int.natAbs_natCast] at hadd
    simp only [List.map_cons,List.sum_cons]
    have hm:=Nat.mul_le_mul_left a.1.natAbs ha
    nlinarith

theorem survivingDominance:Targets.SurvivingRemainderDominance:=by
  intro R row hp hv entry he hnonzero hmax hR
  let rest:=row.erase entry
  have hperm:row.Perm (entry::rest):=List.perm_cons_erase he
  have hpair:(entry::rest).Pairwise (fun a b=>a.2.2≠b.2.2):=
    (List.Perm.pairwise_iff (R:=fun a b:Int×Nat×Nat=>a.2.2≠b.2.2)
      (fun {x y} h=>Ne.symm h) hperm).mp hp
  have hrest:∀b∈rest,b∈row:=by
    intro b hb
    exact hperm.mem_iff.mpr (List.mem_cons_of_mem entry hb)
  have hstrict:∀b∈rest,b.2.2<entry.2.2:=by
    intro b hb
    have hn:entry.2.2≠b.2.2:=(List.pairwise_cons.mp hpair).1 b hb
    have hl:=hmax b (hrest b hb)
    omega
  have hd:=hv entry he
  let U:=Phi (entry.2.2-1)
  let M:=numericalMass row
  let C:=(rest.map (fun b=>b.1.natAbs)).sum
  have hfour:4≤entry.2.2:=(le_max_left _ _).trans hd.1
  have hM:2*M≤entry.2.2:=(le_max_right _ _).trans hd.1
  have hs:0<entry.2.2:=by omega
  have hsU:entry.2.2≤U:=by
    have h:=self_lt_Phi (entry.2.2-1)
    dsimp only [U]
    omega
  have hU:4≤U:=four_le_Phi _
  have hMU:2*M≤U:=hM.trans hsU
  have hsum: M=entry.1.natAbs+C:=by
    dsimp only [M,C,numericalMass]
    have h:=(hperm.map (fun b=>b.1.natAbs)).sum_eq
    simpa only [List.map_cons,List.sum_cons] using h
  have hcoef:1≤entry.1.natAbs:=Int.natAbs_pos.mpr hnonzero
  have hCM:C≤M:=by omega
  have hgap:4*M*U≤Phi entry.2.2:=by
    calc
      4*M*U≤2*(U*U):=by nlinarith
      _≤2*2^U:=Nat.mul_le_mul_left 2 (square_le_power U hU)
      _=2^(U+1):=by rw [Nat.pow_succ,Nat.mul_comm]
      _≤2^(2^(U+1)):=(Nat.lt_two_pow_self).le
      _≤Phi entry.2.2:=by
        simpa only [U,Nat.sub_add_cancel hs] using Phi_succ_gap (entry.2.2-1)
  have hvals:∀b∈rest,b.2.1≤2*U:=by
    intro b hb
    have hd:=hv b (hrest b hb)
    have hl:b.2.2≤entry.2.2-1:=by have h:=hstrict b hb;omega
    exact hd.2.2.le.trans (Nat.mul_le_mul_left 2 (Phi_strictMono.monotone hl))
  let lower:Int:=R+(rest.map (fun b=>b.1*(b.2.1:Int))).sum
  have hbound:lower.natAbs≤R.natAbs+2*U*C:=by
    have h:=weighted_abs rest U hvals
    have ha:=Int.natAbs_add_le R ((rest.map (fun b=>b.1*(b.2.1:Int))).sum)
    dsimp only [lower,C]
    omega
  have hprod:2*U*C≤2*U*M:=Nat.mul_le_mul_left (2*U) hCM
  have hlower:lower.natAbs<Phi entry.2.2:=by nlinarith
  have hleading:Phi entry.2.2<(entry.1*(entry.2.1:Int)).natAbs:=by
    simp only [Int.natAbs_mul,Int.natAbs_natCast]
    have h:entry.2.1≤entry.1.natAbs*entry.2.1:=by nlinarith
    exact hd.2.1.trans_le h
  have habs: |lower| < |entry.1*(entry.2.1:Int)| :=by
    have hnat:=hlower.trans hleading
    have hcast:(lower.natAbs:Int)<((entry.1*(entry.2.1:Int)).natAbs:Int):=by exact_mod_cast hnat
    simpa only [Int.natCast_natAbs] using hcast
  have hpositive:0<(entry.2.1:Int):=by
    have h:=four_le_Phi entry.2.2
    exact_mod_cast (show 0<entry.2.1 by omega)
  have hvsum:=(hperm.map (fun b=>b.1*(b.2.1:Int))).sum_eq
  have hvalue:numericalValue R row=entry.1*(entry.2.1:Int)+lower:=by
    unfold numericalValue
    rw [hvsum]
    simp only [List.map_cons,List.sum_cons]
    dsimp only [lower]
    ring
  rw [hvalue]
  by_cases hc:0<entry.1
  · have hm:=mul_pos hc hpositive
    rw [abs_of_pos hm] at habs
    have hl:=neg_abs_le lower
    have hpos:0<entry.1*(entry.2.1:Int)+lower:=by linarith
    rw [Int.sign_eq_one_of_pos hpos,Int.sign_eq_one_of_pos hc]
  · have hneg:entry.1<0:=by omega
    have hm:=mul_neg_of_neg_of_pos hneg hpositive
    rw [abs_of_neg hm] at habs
    have hl:=le_abs_self lower
    have hs:entry.1*(entry.2.1:Int)+lower<0:=by linarith
    rw [Int.sign_eq_neg_one_of_neg hs,Int.sign_eq_neg_one_of_neg hneg]
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedNumerical.Proof
