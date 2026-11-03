module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedRowTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedNumericalProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.Proof

private theorem maximum_bound {xs:List Nat} {x:Nat} (hx:x∈xs):x≤maximum xs:=by
  induction xs with
  | nil=>cases hx
  | cons a xs ih=>
    rcases List.mem_cons.mp hx with h|h
    · subst x;exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

private theorem positive_sum (cs bs:List Nat) (hl:cs.length=bs.length)
    (hp:∀c∈cs,1≤c):bs.sum≤(cs.zipWith (·*·) bs).sum:=by
  induction cs generalizing bs with
  | nil=>cases bs <;>simp_all
  | cons c cs ih=>
    cases bs with
    | nil=>simp at hl
    | cons b bs=>
      have hc:=hp c List.mem_cons_self
      have ht:=ih bs (by simpa using hl) (fun d hd=>hp d (List.mem_cons_of_mem c hd))
      have hm:b≤c*b:=by simpa only [Nat.one_mul] using Nat.mul_le_mul_right b hc
      simp only [List.zipWith_cons_cons,List.sum_cons]
      omega

private theorem bounded_sum (A:Nat) (cs bs:List Nat) (hl:cs.length=bs.length)
    (hp:∀c∈cs,c≤A):(cs.zipWith (·*·) bs).sum≤A*bs.sum:=by
  induction cs generalizing bs with
  | nil=>cases bs <;>simp_all
  | cons c cs ih=>
    cases bs with
    | nil=>simp at hl
    | cons b bs=>
      have hc:=hp c List.mem_cons_self
      have ht:=ih bs (by simpa using hl) (fun d hd=>hp d (List.mem_cons_of_mem c hd))
      have hm:c*b≤A*b:=Nat.mul_le_mul_right b hc
      simp only [List.zipWith_cons_cons,List.sum_cons,Nat.mul_add]
      omega

private theorem weighted_bound (C:Nat) (rs:List Int) (bs:List Nat) (hl:rs.length=bs.length)
    (hp:∀r∈rs,r.natAbs≤C):
    ((rs.zipWith (fun r b=>r*(b:Int)) bs).sum).natAbs≤C*bs.sum:=by
  induction rs generalizing bs with
  | nil=>cases bs <;>simp_all
  | cons r rs ih=>
    cases bs with
    | nil=>simp at hl
    | cons b bs=>
      have hr:=hp r List.mem_cons_self
      have ht:=ih bs (by simpa using hl) (fun t hm=>hp t (List.mem_cons_of_mem r hm))
      have ha:=Int.natAbs_add_le (r*(b:Int)) ((rs.zipWith (fun t b=>t*(b:Int)) bs).sum)
      simp only [Int.natAbs_mul,Int.natAbs_natCast] at ha
      have hm:r.natAbs*b≤C*b:=Nat.mul_le_mul_right b hr
      change (r*(b:Int)+(rs.zipWith (fun t b=>t*(b:Int)) bs).sum).natAbs≤C*(b+bs.sum)
      rw [Nat.mul_add]
      omega

theorem basisBounds:Targets.ActualBasisBounds:=by
  intro basis row hf a ha
  have hshape:=hf.2 a ha
  have hpos:=positive_sum a.2.coefficients basis hshape.1 hshape.2
  have hmax:∀c∈a.2.coefficients,c≤multiplierMaximum row:=by
    intro c hc
    have hm:c∈row.atoms.flatMap (fun a=>a.2.coefficients):=List.mem_flatMap.mpr ⟨a,ha,hc⟩
    exact (maximum_bound hm).trans (le_max_right _ _)
  have hupper:=bounded_sum (multiplierMaximum row) a.2.coefficients basis hshape.1 hmax
  have hoff:normOffset a.2≤offsetMaximum row:=
    maximum_bound (List.mem_map.mpr ⟨a,ha,rfl⟩)
  have hnorm:actualOrdinalNorm a.2.head.1.repr≤normMaximum row:=
    maximum_bound (List.mem_map.mpr ⟨a,ha,rfl⟩)
  refine ⟨?_,?_,hnorm⟩
  · unfold input
    omega
  · unfold input
    omega

theorem remainderBound:Targets.ActualRemainderBound:=by
  intro basis row hf
  have hmax:∀r∈row.remainder,r.natAbs≤outsideMaximum row:=by
    intro r hr
    exact maximum_bound (List.mem_map.mpr ⟨r,hr,rfl⟩)
  have hw:=weighted_bound (outsideMaximum row) row.remainder basis hf.1 hmax
  have ha:=Int.natAbs_add_le row.constant
    ((row.remainder.zipWith (fun r b=>r*(b:Int)) basis).sum)
  unfold remainderValue
  omega
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.Proof
