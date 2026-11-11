module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesTargets
open OriginalVariableLeaves UniformCertificateCompletion
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- A proved witness for the ORIGINAL outer decoder, not an assumed guard. -/
def ActualOriginalVariableContextGuardSelection : Prop :=
  ∀ n : Nat, ∃ guard : Program 1, ContextGuardCalibrated n guard

/-- Entire original total leaf outputs on ALL input vectors, including failed
outer Context decoding, arbitrary raw type/index and every encoded Gamma. -/
def ActualOriginalVariableLeavesRefinementEquality : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (guard : Program 1) (data : Data),
  ContextGuardCalibrated n guard →
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  ∀ v : List.Vector Nat 2,
    evaluate (refineData guard data).oldSource v = evaluate data.oldSource v ∧
    evaluate (refineData guard data).oldTarget v = evaluate data.oldTarget v

/-- Independent arithmetic branch laws for concrete ASTs, with no native
calibration premise and no arbitrary-calibrated-leaf transport assertion. -/
def ActualOriginalVariableLeavesInternalBranches : Prop :=
  ∀ (guard : Program 1) (data : Data), BranchLaws guard data

/-- Select ONE strengthened initial tuple before all windows/runtime Gamma.
Every prior SAME-final property, including the entire current Package and
native accessibility results, is retained at the exact existing finalData
pipeline of refineInputs guard p. No final weakening law is claimed here. -/
def ActualOriginalVariableLeavesGlobalSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ (p : GlobalSourcePackage.Inputs) (guard : Program 1),
    GlobalSourcePackage.InputsCalibrated n arity p ∧
    ContextGuardCalibrated n guard ∧
    GlobalSourcePackage.InputsCalibrated n arity (refineInputs guard p) ∧
    OriginalFinalNativeAccessibility.Properties n arity (refineInputs guard p) ∧
    BranchLaws guard p.base ∧
    (∀ v : List.Vector Nat 2,
      evaluate (refineInputs guard p).base.oldSource v = evaluate p.base.oldSource v ∧
      evaluate (refineInputs guard p).base.oldTarget v = evaluate p.base.oldTarget v)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesTargets
