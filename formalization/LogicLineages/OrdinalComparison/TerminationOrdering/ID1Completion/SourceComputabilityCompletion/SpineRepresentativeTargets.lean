module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineRepresentativeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineRepresentativeTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open SourceComputabilityCompletion.SpineRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- SAME original numeric calibrations on EVERY raw input and parameter,
including malformed contexts/types and nonclosed windows. Global tuple and
window AST are chosen before every concrete window or Gamma. -/
def ActualOriginalSpineRepresentativeCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data) (window : Program 1),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  (∀ v, evaluate window v = GuardCalibration.validWindowValue n v) →
  InternalOriginalUniformDescentSelection.Calibrated n arity (baseData data window)

/-- Arbitrary actual measure output is preserved in BOTH directions by
the literal representative checker under its actual active guard. No shape,
evaluation, leaf-calibration or semantic-to-derivability premise occurs. -/
def ActualParameterizedRepresentativeSpinePreservation : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (window : Program 1)
    (α : Type) (Delta : List (Formula α))
    (out value parameter mark : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((activeGraph data window value parameter).imp
      ((representativeGraph data window out value parameter).imp
        ((BottomSpineMeasure.graph mark out).iff (BottomSpineMeasure.graph mark value)))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineRepresentativeTargets
