module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafTargets
open OriginalConstructorLeaf
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal output equality on EVERY raw input, not merely equivalence of
acceptance on valid windows. The original total leafValue, malformed and
zero-rejection branches, Context/Object and StepCertificate encodings remain.
No successful decoding, subtype closure, strict precedence or fixed Gamma
premise is permitted. -/
def ActualOriginalConstructorLeafRefinementEquality : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (oldStep : Program 4),
  InternalOriginalUniformApplicationStepSelection.LeafCalibrated n arity oldStep →
  ∀ v : List.Vector Nat 4, evaluate (refined oldStep) v = evaluate oldStep v

/-- Direct internal inversion of the concrete Program AST for ANY oldStep.
Calibration is not an internal correctness oracle. Both raw constructor laws
and the complete original acceptance factor are proved conclusions. -/
def ActualOriginalConstructorLeafInternalCases : Prop :=
  ∀ oldStep : Program 4,
    OriginalFactor oldStep (refined oldStep) ∧ ConstructorCases (refined oldStep)

/-- ONE global original input tuple and its ONE literal refinement are
selected before ALL windows, Gamma, raw values and symbolic formulas. Native
calibration, full equality, complete original R005 Package and constructor
laws are conclusions, not supplied fields or assumptions. All other AST
fields stay literally p's; source, comp and lift use the SAME refined tuple.
No independent source is selected for different constructors or windows.
This does not assert quotient/path inversion, representative rigidity,
variable computability, auxiliary-term substitution or closed all-term ID1. -/
def ActualOriginalConstructorLeafGlobalSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ p : GlobalSourcePackage.Inputs,
    GlobalSourcePackage.InputsCalibrated n arity p ∧
    (let q := refineInputs p
     (∀ v : List.Vector Nat 4, evaluate q.oldStep v = evaluate p.oldStep v) ∧
     GlobalSourcePackage.InputsCalibrated n arity q ∧
     GlobalSourcePackage.Package n arity
       (GlobalSourcePackage.source q) (GlobalSourcePackage.computability q)
       (GlobalSourcePackage.lift q) ∧
     OriginalFactor p.oldStep q.oldStep ∧ ConstructorCases q.oldStep)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafTargets
