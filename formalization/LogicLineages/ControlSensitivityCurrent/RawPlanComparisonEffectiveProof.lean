module
public import LogicLineages.ControlSensitivityCurrent.RawPlanComparisonTargets
public import LogicLineages.ControlSensitivityCurrent.RawPlanCompilerEffectiveProof
public import LogicLineages.ControlSensitivityCurrent.RawDerivedCompositionPrimitiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanComparison

theorem compare_result_effective : Computable compareResult := by
  let A := PlanCompiler.ResultCode
  let B := A × (Code × Code)
  let C := B × Code
  let D := C × Code
  have haggregate := DerivedComposition.effective.2.1.comp
    (Computable.fst.pair (Computable.snd.comp (Computable.snd : Computable (fun p : A => p.2))))
  have hp : Computable (fun p : B => p.2) := Computable.snd
  have hwrapRight := DerivedComposition.effective.2.2.comp
    ((Computable.const true).pair (Computable.snd.comp hp))
  have hwrapLeft := DerivedComposition.effective.2.2.comp
    ((Computable.const false).pair (Computable.fst.comp (hp.comp
      (Computable.fst : Computable (fun p : C => p.1)))))
  have hraw : Computable (fun p : D => p.1.1.2) := hp.comp (Computable.fst.comp Computable.fst)
  have hstrict := (Computable.snd.comp hraw).pair (Computable.fst.comp hraw)
  have hweak := (Computable.snd.comp (Computable.fst : Computable (fun p : D => p.1))).pair
    Computable.snd
  have hfinish := Computable.option_some.comp (hstrict.pair hweak)
  apply (Computable.option_bind haggregate
    (Computable.option_bind hwrapRight (Computable.option_bind hwrapLeft hfinish.to₂).to₂).to₂).of_eq
  intro r
  cases h : DerivedComposition.aggregate r.1 r.2.2 with
  | none => simp [compareResult, h]
  | some p => cases p <;> simp [compareResult, h]

theorem effective : RawPlanComparisonTargets.Effective :=
  Computable.option_bind PlanCompiler.effective (compare_result_effective.comp Computable.snd).to₂

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanComparison
