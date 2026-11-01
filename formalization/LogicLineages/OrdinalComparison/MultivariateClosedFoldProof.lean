module
public import LogicLineages.OrdinalComparison.MultivariateDirectNormalizeTargets
public import LogicLineages.OrdinalComparison.MultivariatePositiveRayProof
public import LogicLineages.OrdinalComparison.MultivariateFreshProbeProof
public import LogicLineages.OrdinalComparison.EncodedPositiveFoldProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariateDirectNormalize

attribute [local irreducible] Phi actualCollapse encodedPositiveFoldValue encodedMultivariateRay

theorem closed_fold : Targets.MultivariateClosedFoldProgram := by
  refine ⟨?_,?_⟩
  · have hr : Primrec (fun n : Nat => encodedMultivariateRay 1 n) :=
      MultivariatePositiveRay.code.2.1.comp (Primrec.const 1) Primrec.id
    exact encodedPositiveFoldComputable.comp hr.to_comp
  · intro E
    unfold encodedMultivariateClosedValue
    rw [MultivariatePositiveRay.code.2.2 1 E,encodedPositiveFoldSourceCorrect]
    simpa only [Nat.mul_zero] using MultivariatePositiveRay.source.2.2.2.1 E 1 0

theorem probe_support (cap : Nat) (E : MultivariatePositiveExpr) :
    positiveExprHasInput (multivariatePositiveProbe cap E)=multivariatePositiveHasInput E := by
  induction E with
  | constant c => rfl
  | input i => rfl
  | add E F ihE ihF => exact congrArg₂ Bool.or ihE ihF
  | head rho E ih => exact ih

theorem input_absent (E : MultivariatePositiveExpr) (ha : multivariatePositiveHasInput E=false)
    (rho sigma : Nat → Nat) : actualMultivariatePositiveEval E rho=actualMultivariatePositiveEval E sigma := by
  induction E with
  | constant c => rfl
  | input i => cases ha
  | add E F ihE ihF =>
    have hp : multivariatePositiveHasInput E=false ∧ multivariatePositiveHasInput F=false :=
      Bool.or_eq_false_iff.mp ha
    exact congrArg₂ (·+·) (ihE hp.1) (ihF hp.2)
  | head head E ih => exact congrArg (actualProfileHead head) (ih ha)

theorem closed_probe_fold (cap : Nat) (E : MultivariatePositiveExpr)
    (ha : multivariatePositiveHasInput E=false) :
    encodedPositiveFoldValue (positiveExprEncode (multivariatePositiveProbe cap E))=
      encodedMultivariateClosedValue (multivariatePositiveEncode E) := by
  rw [encodedPositiveFoldSourceCorrect,MultivariateFreshProbe.source.2.1 cap 0 E,closed_fold.2 E]
  exact input_absent E ha _ _

end LogicLineages.OrdinalComparison.MultivariateDirectNormalize
