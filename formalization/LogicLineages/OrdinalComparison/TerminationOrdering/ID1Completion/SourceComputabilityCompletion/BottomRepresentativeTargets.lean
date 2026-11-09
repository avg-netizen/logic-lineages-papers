module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomRepresentativeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomRepresentativeTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open SourceComputabilityCompletion.BottomRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Original calibration on ALL raw values and parameters, including bad
context/source codes and nonclosed windows. The same base Data and window
program are selected before any window or Gamma. No new source convention. -/
def ActualOriginalBottomRepresentativeCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data) (window : Program 1),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  (∀ v, evaluate window v = GuardCalibration.validWindowValue n v) →
  InternalOriginalUniformDescentSelection.Calibrated n arity (baseData data window) ∧
    InternalOriginalUniformDescentSelection.Calibrated n arity (readyData data window)

/-- The literal representative wrapper preserves the exact bottom-test
output at source-valid activated inputs. Both directions follow from the
same internal derivation, without interpreting an opaque leaf semantically. -/
def ActualParameterizedRepresentativeBottomPreservation : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (window : Program 1)
    (α : Type) (Delta : List (Formula α))
    (out value parameter indicator : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((activeGraph data window value parameter).imp
      ((representativeGraph data window out value parameter).imp
        ((bottomGraph indicator out).iff (bottomGraph indicator value)))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomRepresentativeTargets
