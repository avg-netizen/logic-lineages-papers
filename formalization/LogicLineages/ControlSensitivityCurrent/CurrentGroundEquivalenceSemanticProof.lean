module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundEquivalenceTargets
public import LogicLineages.ControlSensitivityCurrent.SourceASTObservationProof
public import LogicLineages.ControlSensitivityCurrent.CompilerCompositionProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundEquivalence

open LogicLineages.OrdinalComparison.Source GroundEquivalence ExistentialPlan
open PolicyProgramComparisonTargets (Weak Strict)

theorem counter_iff (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ : List Ty}
    (ρ : Variable Γ .ground → Nat) (a b : Input Γ .ground) (weakQuery : Bool) :
    (counterexample weakQuery a b).eval p f ρ Fin.elim0 ↔
      if weakQuery then PolicyCollision.rawScalar p f (inputs ρ) b.term <
        PolicyCollision.rawScalar p f (inputs ρ) a.term
      else PolicyCollision.rawScalar p f (inputs ρ) b.term ≤
        PolicyCollision.rawScalar p f (inputs ρ) a.term := by
  have hb := SourceAST.sourceValue_rename p f (Renaming.weaken Γ .ground) ρ
    (extend ρ (InputNormalization.sourceValue p f ρ a)) (fun _ => rfl) b
  have hpa := (PolicyObservation.observationCalibration p f Γ (inputs ρ) a.term).1
  have hpb := (PolicyObservation.observationCalibration p f Γ (inputs ρ) b.term).1
  cases weakQuery <;>
    simp only [counterexample, Bool.false_eq_true, ite_false, ite_true,
      InputNormalization.Input.eval, Fin.cases_zero, InputNormalization.Node.eval,
      PrimitiveLowering.Port.value, SourceSortCompletion.input, inputs, extend, hb, decide_eq_true_eq] <;>
    simp only [InputNormalization.sourceValue] <;> omega

theorem reductions_semantic (n : Nat) (a b : Input (List.replicate n Ty.ground) .ground)
    (f : Nat → Nat) (hf : FullAddition.Targets.SourceGrowth f) (p : AdmissibleSum.Policy) :
    let pw := InputNormalization.normalize .nil (counterexample true a b)
    let ps := InputNormalization.normalize .nil (counterexample false a b)
    (Weak p f a.term b.term ↔
      Strict p f (BooleanCompiler.strictPair pw).1.term (BooleanCompiler.strictPair pw).2.term) ∧
    (Strict p f a.term b.term ↔
      Weak p f (BooleanCompiler.weakPair ps).1.term (BooleanCompiler.weakPair ps).2.term) := by
  have hw := (CompilerComposition.sharedCorrect f hf p n (counterexample true a b)).1
  have hs := (CompilerComposition.sharedCorrect f hf p n (counterexample false a b)).2
  constructor
  · exact ((hw.trans (by simp [counter_iff, PolicyProgramComparisonTargets.Weak, not_exists, Nat.not_lt])).symm)
  · exact ((hs.trans (by simp [counter_iff, PolicyProgramComparisonTargets.Strict, not_exists, Nat.not_le])).symm)

end LogicLineages.ControlSensitivityCurrent.CurrentGroundEquivalence
