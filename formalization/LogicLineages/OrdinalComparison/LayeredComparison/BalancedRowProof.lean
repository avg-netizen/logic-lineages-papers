module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBasisProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.Proof

private theorem basis_member_le_sum {xs:List Nat} {x:Nat} (hx:x∈xs):x≤xs.sum:=by
  induction xs with
  | nil=>cases hx
  | cons a xs ih=>
    rcases List.mem_cons.mp hx with h|h
    · subst x;simp only [List.sum_cons];omega
    · have ht:=ih h;simp only [List.sum_cons];omega

theorem largeWindow:Targets.ActualLargeWindow:=by
  intro basis row hf hlarge selected hs hmin
  have hA:1≤multiplierMaximum row:=le_max_left _ _
  have hselected:=basisBounds basis row hf selected hs
  constructor
  · intro a ha
    have hb:=basisBounds basis row hf a ha
    have hw:=BalancedNumerical.Proof.exactWindow row.constant (coefficientMass row)
      (outsideMaximum row) (multiplierMaximum row) (offsetMaximum row) (normMaximum row)
      basis.sum (input basis selected.2) (input basis a.2) hA (hlarge selected hs)
      hselected.1 (hmin a ha) hb.2.1
    exact ⟨(Nat.add_le_add_right hb.2.2 2).trans hw.2.2.2,hmin a ha,hw.2.1⟩
  · intro a ha
    have hb:=basisBounds basis row hf a ha
    have hw:=BalancedNumerical.Proof.exactWindow row.constant (coefficientMass row)
      (outsideMaximum row) (multiplierMaximum row) (offsetMaximum row) (normMaximum row)
      basis.sum (input basis a.2) (input basis a.2) hA (hlarge a ha)
      hb.1 le_rfl hb.2.1
    have hr:=remainderBound basis row hf
    have hm:=Nat.mul_le_mul_left (outsideMaximum row) hb.1
    have hbound:(remainderValue basis row).natAbs≤
        row.constant.natAbs+outsideMaximum row*input basis a.2:=
      hr.trans (Nat.add_le_add_left hm row.constant.natAbs)
    exact (Nat.mul_le_mul_left 4 hbound).trans_lt hw.2.2.1

theorem smallBasisBound:Targets.ActualSmallBasisBound:=by
  intro basis row hf a ha hsmall
  have hsum:basis.sum<threshold row:=
    ((basisBounds basis row hf a ha).1).trans_lt hsmall
  refine ⟨hsum,?_⟩
  intro x hx
  exact (basis_member_le_sum hx).trans_lt hsum
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.Proof
