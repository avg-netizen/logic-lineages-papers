module
public import LogicLineages.OrdinalComparison.SourceBooleanCompilerObservationProof
public import LogicLineages.OrdinalComparison.SourceBooleanPlanProof
public import LogicLineages.OrdinalComparison.SourceBinaryPlanProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.BooleanCompiler.Proof
open PrimitiveLowering

theorem lower_correct (Γ : List Ty) (p : Program Γ) :
    ∀ ρ : Variable Γ .ground → Nat, Eval ρ p ↔ ExistentialPlan.Eval ρ (lower p) := by
  induction p with
  | @matrix Γ n m d a root =>
    intro ρ
    exact (BooleanPlan.Proof.matrixExact Γ n m d a root ρ).symm
  | @add Γ a b q ih =>
    intro ρ
    change Eval (ExistentialPlan.extend ρ (a.value (ExistentialPlan.inputs ρ)+b.value (ExistentialPlan.inputs ρ))) q ↔
      ∃ n, (Gate.add (ExistentialPlan.portRename (Renaming.weaken Γ .ground) a)
        (ExistentialPlan.portRename (Renaming.weaken Γ .ground) b) (.var .here)).Holds
          (ExistentialPlan.inputs (ExistentialPlan.extend ρ n)) ∧
        ExistentialPlan.Eval (ExistentialPlan.extend ρ n) (lower q)
    simp only [add_binding,← ih,exists_eq_left]
  | @literal Γ k q ih =>
    intro ρ
    exact (ih _).trans (BinaryPlan.Proof.literalCorrect Γ ρ k (lower q)).symm
  | @observation Γ t q ih =>
    intro ρ
    change Eval (ExistentialPlan.extend ρ (sourceValue ρ t)) q ↔ ∃ n,
      SourceAdditionCompletion.Equation (ExistentialPlan.inputs (ExistentialPlan.extend ρ n))
        (ScopedDAG.renameInput (Renaming.weaken Γ .ground) t).term (ScopedDAG.variableInput .here).term ∧
        ExistentialPlan.Eval (ExistentialPlan.extend ρ n) (lower q)
    simp only [observation_binding,← ih,exists_eq_left]
  | @unary Γ h x q ih =>
    intro ρ
    change Eval (ExistentialPlan.extend ρ (sourceValue ρ (call h x))) q ↔ ∃ n,
      SourceAdditionCompletion.Equation (ExistentialPlan.inputs (ExistentialPlan.extend ρ n))
        (ScopedDAG.renameInput (Renaming.weaken Γ .ground) (call h x)).term (ScopedDAG.variableInput .here).term ∧
        ExistentialPlan.Eval (ExistentialPlan.extend ρ n) (lower q)
    simp only [observation_binding,← ih,exists_eq_left]
end LogicLineages.OrdinalComparison.Source.BooleanCompiler.Proof
