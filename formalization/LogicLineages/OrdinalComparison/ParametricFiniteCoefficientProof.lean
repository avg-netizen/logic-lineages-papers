module
public import LogicLineages.OrdinalComparison.ParametricFiniteCoefficientMaximumProof
public import LogicLineages.OrdinalComparison.ParametricActualCollapseProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricFiniteCoefficient.Proof
open ParametricFinitePairCollapse

theorem finiteBoundary : Targets.FiniteBoundary := by
  intro G hi b
  constructor
  · have h := ParametricActualCollapse.Proof.finiteValues G hi b
    simpa only [value,ordinal,Nat.cast_zero,mul_zero,zero_add] using h
  · simp [formula]

theorem exactFiniteCoefficient : Targets.ExactFiniteCoefficient := by
  intro G hm hi a
  induction a using Nat.strong_induction_on with
  | h a iha =>
    intro b
    induction b using Nat.strong_induction_on with
    | h b ihb =>
      cases a with
      | zero => simpa [Function.iterate_zero] using (finiteBoundary G hi b).1
      | succ a =>
        have he : ∀ q ∈ predecessors G (a+1,b),value G q=formula G q := by
          rintro ⟨u,v⟩ hq
          have hlt := ((ParametricFinitePairCollapse.Proof.predecessor_test G (a+1,b) (u,v)).mp hq).1
          rcases hlt with hu | ⟨hu,hv⟩
          · exact iha u hu v
          · change u = a+1 at hu
            change v < b at hv
            subst u
            exact ihb v hv
        change value G (a+1,b)=formula G (a+1,b)
        rw [ParametricFinitePairCollapse.Proof.exactMaximum]
        obtain ⟨hw,hn,hvalue,hbound⟩ := exactMaximizer G hm hi a b
        apply Nat.le_antisymm
        · apply Finset.sup_le
          intro q hq
          rw [he q hq]
          exact hbound q hq
        · have h := Finset.le_sup (f:=fun q => value G q+1) hw
          rw [he _ hw,hvalue] at h
          exact h
end LogicLineages.OrdinalComparison.Source.ParametricFiniteCoefficient.Proof
