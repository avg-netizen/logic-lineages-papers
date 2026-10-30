module
public import LogicLineages.OrdinalComparison.LinkedResidueLaurentTargets
public import LogicLineages.OrdinalComparison.LinkedResidueProof
public import LogicLineages.OrdinalComparison.PrimitiveRootDerivativeProof
public import LogicLineages.OrdinalComparison.PrimitiveRootComplementProof
public import LogicLineages.OrdinalComparison.SimplePoleLaurentProof
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section
universe u
namespace LogicLineages.OrdinalComparison

theorem actualLinkedResidueFormula : Targets.ActualLinkedResidueFormula.{u} := by
  intro K _ _ u hu z hz
  obtain ⟨hr, hD, heD, hpos, hupper, hqb, huB, hqd, hdq, hmq, hcomp⟩ :=
    actualLinkedResidueArithmetic u (by omega)
  have hodd : Odd (actualLinkedModulus u) := by
    refine ⟨2 ^ (actualLinkedHalfExponent u - 1), ?_⟩
    unfold actualLinkedModulus
    have h := Nat.sub_add_cancel (show 1 ≤ actualLinkedHalfExponent u by omega)
    conv_lhs => rw [← h, pow_succ]
    ring
  have hq : actualLinkedModulus u ≠ 0 := Nat.succ_ne_zero _
  have hz0 : z ≠ 0 := (hz.isUnit hq).ne_zero
  have he : 1 ≤ actualLinkedOffset u := by unfold actualLinkedOffset; omega
  have heq : actualLinkedOffset u - 1 + 1 = actualLinkedOffset u := by omega
  obtain ⟨ha, hder⟩ := actualPrimitiveRootSourceDerivative K _ _ hodd hqd hdq z hz
  have hn := actualPrimitiveRootSourceDerivativeNonzero K _ _ hodd hqd hdq z hz
  let A := (actualBinarySourceDenominator (actualLinkedCutoff u)).map (algebraMap (ZMod 2) K)
  have ha' : A.eval z = 0 := by simpa [A, Polynomial.eval_map] using ha
  have hn' : A.derivative.eval z ≠ 0 := by
    simpa [A, Polynomial.derivative_map, Polynomial.eval_map] using hn
  have hres := actualSimplePoleExpansionResidue K A
    (Polynomial.X ^ (actualLinkedOffset u - 1)) z ha' hn'
  have hfirst : (actualLinkedResidueExpansion u z).coeff (-1) =
      z ^ actualLinkedOffset u / Polynomial.eval₂ (algebraMap (ZMod 2) K) z
        (actualBinarySourceDenominator (actualLinkedCutoff u - actualLinkedModulus u)) := by
    change (actualSimplePoleExpansion A _ z).coeff (-1) = _
    rw [hres]
    simp only [Polynomial.eval_pow, Polynomial.eval_X, A, Polynomial.derivative_map,
      Polynomial.eval_map, hder, div_mul_eq_div_div, div_inv_eq_mul]
    rw [← pow_succ, heq]
  have ht := actualPrimitiveRootComplement K _ _ hodd hmq z hz
  have hsecond : (actualLinkedResidueExpansion u z).coeff (-1) =
      z ^ ((actualLinkedOffset u : Int) - (actualLinkedDegree u : Int)) *
        Polynomial.eval₂ (algebraMap (ZMod 2) K) z
          (actualBinarySourceDenominator (actualLinkedTail u)) := by
    rw [hfirst, hcomp, div_eq_mul_inv, ht, zpow_sub₀ hz0]
    simp only [zpow_natCast, actualLinkedDegree]
    ring
  have hpart := actualPrimitiveRootPartialProductNonzero K (actualLinkedModulus u)
    (actualLinkedCutoff u - actualLinkedModulus u) (by omega) z hz
  refine ⟨hfirst, hsecond, ?_, ?_⟩
  · rw [hfirst]
    exact div_ne_zero (pow_ne_zero _ hz0) hpart
  · exact actualSimplePoleExpansionLowerSupport K A _ z ha' hn'

theorem fullActualSourceResidue : Targets.FullActualSourceResidue.{u} := by
  intro K _ _ v hv z hz
  apply actualLinkedResidueFormula K (Phi v) (by have := self_lt_Phi v; omega) z hz

end LogicLineages.OrdinalComparison
