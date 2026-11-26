module
public import LogicLineages.PermittedControl.RelativeDescentTargets
public import LogicLineages.PermittedControl.RelativeNormProof
public import LogicLineages.PermittedControl.EntryExistenceProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem relativeMaximumSpec : Targets.RelativeMaximumSpec := by
  intro mu rho b ha hr hb
  have hm : mu < epsilonZero := (le_self_add : mu ≤ mu+rho).trans_lt ha
  have hpos : 0 < mu+rho := hr.trans_le le_add_self
  have hmax := actualMaximumPredecessor_correct (mu+rho) hpos ha b
  have hmlo : mu ≤ actualMaximumPredecessor (mu+rho) b := hmax.2 ⟨by
    simpa using (add_lt_add_iff_left mu).mpr hr, hb⟩
  have hrecon : actualMaximumPredecessor (mu+rho) b = mu + relativeMaximum mu rho b :=
    (Ordinal.add_sub_cancel_of_le hmlo).symm
  have hrlt : relativeMaximum mu rho b < rho := by
    apply (add_lt_add_iff_left mu).mp
    rw [← hrecon]
    exact hmax.1.1
  have hrbelow : relativeMaximum mu rho b < epsilonZero :=
    hrlt.trans_le (le_add_self : rho ≤ mu+rho) |>.trans ha
  have hnorm := (relativeNorm mu (relativeMaximum mu rho b) hm hrbelow).1
  refine ⟨hrecon, ⟨hrlt, ?_⟩, ?_⟩
  · rw [← hnorm, ← hrecon]
    exact hmax.1.2
  · intro y hy
    have hybelow : y < epsilonZero := (hy.1.trans_le (le_add_self : rho ≤ mu+rho)).trans ha
    have hycost := (relativeNorm mu y hm hybelow).1
    apply (add_le_add_iff_left mu).mp
    rw [← hrecon]
    exact hmax.2 ⟨(add_lt_add_iff_left mu).mpr hy.1, by rw [hycost]; exact hy.2⟩

 theorem relativeDescentStep : Targets.RelativeDescentStep := by
  intro f mu y ha hmu hy hb
  have hybelow : y < epsilonZero := (le_add_self : y ≤ mu+y).trans_lt ha
  have hd := actualNonfiniteDecomposition y hy hybelow
  have hlim : Order.IsSuccLimit (mu+actualLimitPart y) := Ordinal.isSuccLimit_add mu hd.2.1
  have hlp : actualLimitPart (mu+y) = mu+actualLimitPart y := by
    conv_lhs => rw [hd.2.2.1, ← add_assoc]
    exact limitPart_tail _ hlim _
  have hbnd : mu+actualLimitPart y < epsilonZero :=
    (add_le_add_right (Ordinal.mul_div_le y Ordinal.omega0) mu).trans_lt ha
  refine ⟨hlp, ?_⟩
  unfold descentWith
  rw [hlp]
  exact (relativeMaximumSpec mu (actualLimitPart y) _ hbnd hd.2.1.bot_lt hb).1

end LogicLineages.PermittedControl
