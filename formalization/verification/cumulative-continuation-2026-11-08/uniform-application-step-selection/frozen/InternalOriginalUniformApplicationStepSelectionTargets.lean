module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationStepSelectionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationStepSelectionTargets
open Source InternalOriginalUniformApplicationStepSelection
open InternalOriginalUniformDescentSelection (Data)
open InternalOriginalUniformParameterLeaves (parameterCode)
open InternalParameterizedApplicationStepChecker (StepCalibratedAt)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- One old-step AST precedes every source window and Gamma. Both raw-input
calibration and all original context slices are retained, including malformed
source, target and step-certificate inputs. -/
def ActualOriginalUniformStepLeafProgram : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat), ∃ oldStep : Program 4,
    LeafCalibrated n arity oldStep ∧
    ∀ (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
      StepCalibratedAt n arity symbols S Gamma table oldStep
        (parameterCode symbols S Gamma table)

/-- For each globally calibrated canonical Data tuple, one globally chosen
old-step leaf supplies the concrete selected original checker, its all-input
context calibration and its internal original application-step law. No
subtype-closure, source-validity or fixed-Gamma premise is added to calibration. -/
def ActualOriginalUniformApplicationStepSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  ∃ oldStep : Program 4, LeafCalibrated n arity oldStep ∧
    SelectedCalibrated n arity data oldStep ∧ InternalLaw data oldStep

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationStepSelectionTargets
