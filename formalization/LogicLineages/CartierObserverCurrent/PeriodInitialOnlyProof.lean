module
public import LogicLineages.CartierObserverCurrent.PeriodInitialOnlyTargets
public import LogicLineages.OrdinalComparison.TranslatedRationalProof
public import LogicLineages.OrdinalComparison.LinkedResidueProof
public import LogicLineages.OrdinalComparison.PrimitiveRootDerivativeProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.PeriodInitialOnly
open LogicLineages.OrdinalComparison

theorem initialResidue : Targets.InitialResidue := by
  intro u hu z
  obtain ⟨hr, hD, heD, hpos, hupper, hqb, huB, hqd, hdq, hmq, hcomp⟩ :=
    actualLinkedResidueArithmetic u (by omega)
  have hodd : Odd (actualLinkedModulus u) := by
    refine ⟨2 ^ (actualLinkedHalfExponent u - 1), ?_⟩
    unfold actualLinkedModulus
    have h := Nat.sub_add_cancel (show 1 ≤ actualLinkedHalfExponent u by omega)
    conv_lhs => rw [← h, pow_succ]
    ring
  have ha := (actualPrimitiveRootSourceDerivative ActualResidueField _ _ hodd hqd hdq
    z.val z.property).1
  have hd := actualPrimitiveRootSourceDerivativeNonzero ActualResidueField _ _ hodd hqd hdq
    z.val z.property
  let A := (actualBinarySourceDenominator (actualLinkedCutoff u)).map
    (algebraMap (ZMod 2) ActualResidueField)
  have ha' : A.eval z.val = 0 := by simpa [A, Polynomial.eval_map] using ha
  have hd' : A.derivative.eval z.val ≠ 0 := by
    simpa [A, Polynomial.derivative_map, Polynomial.eval_map] using hd
  have h := actualTranslatedRationalSimplePole ActualResidueField z.val A
    (Polynomial.X ^ (actualLinkedOffset u - 1)) ha' hd'
  exact congrArg (fun F : HahnSeries Int ActualResidueField => F.coeff (-1)) h

#audit_namespace LogicLineages.CartierObserverCurrent.PeriodInitialOnly
end LogicLineages.CartierObserverCurrent.PeriodInitialOnly
