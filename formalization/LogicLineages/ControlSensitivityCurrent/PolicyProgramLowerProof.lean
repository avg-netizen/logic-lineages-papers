module
public import LogicLineages.ControlSensitivityCurrent.PolicyProgramObservationProof
public import LogicLineages.ControlSensitivityCurrent.PolicyMatrixProof
public import LogicLineages.ControlSensitivityCurrent.PolicyBinaryProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyProgram
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open BooleanCompiler
open PrimitiveLowering

theorem lower_correct (pol : AdmissibleSum.Policy) (f : Nat → Nat) (Γ : List Ty) (p : Program Γ) :
    ∀ ρ : Variable Γ .ground → Nat, InputNormalization.programEval pol f ρ p ↔ PolicyPlan.Eval pol f ρ (lower p) := by
  induction p with
  | @matrix Γ n m d a root =>
    intro ρ
    exact (PolicyMatrix.matrixExact pol f Γ n m d a root ρ).symm
  | @add Γ a b q ih =>
    intro ρ
    change InputNormalization.programEval pol f (ExistentialPlan.extend ρ (a.value (ExistentialPlan.inputs ρ)+b.value (ExistentialPlan.inputs ρ))) q ↔
      ∃ n, (Gate.add (ExistentialPlan.portRename (Renaming.weaken Γ .ground) a)
        (ExistentialPlan.portRename (Renaming.weaken Γ .ground) b) (.var .here)).Holds
          (ExistentialPlan.inputs (ExistentialPlan.extend ρ n)) ∧
        PolicyPlan.Eval pol f (ExistentialPlan.extend ρ n) (lower q)
    simp only [add_binding,← ih,exists_eq_left]
  | @literal Γ k q ih =>
    intro ρ
    exact (ih _).trans (PolicyBinary.literalCorrect pol f Γ ρ k (lower q)).symm
  | @observation Γ t q ih =>
    intro ρ
    change InputNormalization.programEval pol f (ExistentialPlan.extend ρ (InputNormalization.sourceValue pol f ρ t)) q ↔ ∃ n,
      PolicyAddition.Equation pol f (ExistentialPlan.inputs (ExistentialPlan.extend ρ n))
        (ScopedDAG.renameInput (Renaming.weaken Γ .ground) t).term (ScopedDAG.variableInput .here).term ∧
        PolicyPlan.Eval pol f (ExistentialPlan.extend ρ n) (lower q)
    simp only [observation_binding pol f,← ih,exists_eq_left]
  | @unary Γ h x q ih =>
    intro ρ
    change InputNormalization.programEval pol f (ExistentialPlan.extend ρ (InputNormalization.sourceValue pol f ρ (call h x))) q ↔ ∃ n,
      PolicyAddition.Equation pol f (ExistentialPlan.inputs (ExistentialPlan.extend ρ n))
        (ScopedDAG.renameInput (Renaming.weaken Γ .ground) (call h x)).term (ScopedDAG.variableInput .here).term ∧
        PolicyPlan.Eval pol f (ExistentialPlan.extend ρ n) (lower q)
    simp only [observation_binding pol f,← ih,exists_eq_left]
theorem lowering : PolicyProgramTargets.Lowering := by
  intro p f Γ ρ q
  exact lower_correct p f Γ q ρ
end LogicLineages.ControlSensitivityCurrent.PolicyProgram
