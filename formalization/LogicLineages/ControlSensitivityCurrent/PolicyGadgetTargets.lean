module
public import LogicLineages.ControlSensitivityCurrent.PolicyGadgetDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyGadgetTargets
open LogicLineages.OrdinalComparison.Source
open SourceAdditionCompletion SourceSortCompletion ParametricSourceAddition

def SmallShapes : Prop :=
  (∀ n : Nat, AdmissibleSum.Shape n → 0 < n) ∧
  (∀ s : AdmissibleSum.Shape 1, s = .leaf) ∧
  (∀ s : AdmissibleSum.Shape 2, s = .join .leaf .leaf)

def AtomicEraserAssignment : Prop := ∀ p : AdmissibleSum.Policy,
  ∀ (Γ : List Ty) (a b : Atom Γ),
    AdmissibleAssignment.assignment p (eraser a b) = some (eraserVector a b)

def SuccessorAssignment : Prop := ∀ p : AdmissibleSum.Policy,
  ∀ (Γ : List Ty) (x : Variable Γ .ground),
    AdmissibleAssignment.assignment p (successorProbe x) =
      some (fun _ => .collapse .one (.add .one (.var ⟨.ground,x,0⟩)))

def IdentityZeroAssignment : Prop := ∀ p : AdmissibleSum.Policy, ∀ Γ : List Ty,
  AdmissibleAssignment.assignment p (.app (identity (Γ := Γ)) .zeroC) =
    some (PolicyGadget.identityZeroVector Γ)
end LogicLineages.ControlSensitivityCurrent.PolicyGadgetTargets
