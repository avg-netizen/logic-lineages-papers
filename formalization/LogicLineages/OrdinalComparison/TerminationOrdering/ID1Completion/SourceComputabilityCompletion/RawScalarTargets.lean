module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.RawScalarDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.RawScalarTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalOriginalUniformParameterLeaves (parameterCode)
open SourceComputabilityCompletion.RawScalar
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Every raw value is retained, including malformed values and decoded
nonuniverse terms. Data is fixed before all source windows and Gamma. -/
def ActualOriginalRawScalarCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  ∀ (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) → ∀ value : Nat,
    evaluate (checker data) (List.Vector.ofFn ![value,parameterCode symbols S Gamma table]) =
      (NumberedNumericCarrier.canonicalCarrierTest n arity symbols S Gamma value).toNat

/-- A literal original checker derivation for arbitrary Data, symbolic
value/type/parameter, assumptions, and one-body calculus. No calibration is
reflected into this internal proof. -/
def ActualParameterizedTypedScalar : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (α : Type) (Delta : List (Formula α))
    (value typ parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((InternalOriginalUniformDescentSelection.typedAccepted data.oldRepresentative
      (InternalOriginalUniformDescentSelection.validity data) data.member value typ parameter).imp
        (accepted data value parameter)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.RawScalarTargets
