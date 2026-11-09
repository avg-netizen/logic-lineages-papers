module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.Targets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Exact original certificate selectors suffice to open and reconstruct the
same quotient-edge graph at an arbitrary symbolic parameter. -/
def ActualParameterizedQuotientEdgeFactorization : Prop :=
  ∀ (data : Data) (oldStep : Program 4) (body : Positive (Fin 1))
    (α : Type) (Delta : List (Formula α))
    (x y certificate s t k parameter : OTerm α),
  Nonempty (Derivation body Delta
    ((selectors certificate s t k).imp
      ((edgeAccepted data oldStep x y certificate parameter).iff
        (requirements data oldStep x y s t k parameter))))

/-- Original source typing and one original quotient edge imply target
typing at the SAME symbolic p, without semantic calibration, target typing,
raw certificate witnesses or a context-fiber hypothesis. -/
def ActualParameterizedQuotientEdgeTypedPropagation : Prop :=
  ∀ (data : Data) (oldStep : Program 4) (body : Positive (Fin 1))
    (α : Type) (Delta : List (Formula α)) (x y certificate typ parameter : OTerm α),
  Nonempty (Derivation body Delta
    ((typedAccepted data x typ parameter ⊓ edgeAccepted data oldStep x y certificate parameter).imp
      (typedAccepted data y typ parameter)))

/-- Preserve ALL natural inputs, the original certificate code and distinct
source-universe/packed-target semantics. The only mathematical window
hypothesis is the original subtype closure. -/
def ActualOriginalUniformQuotientEdgeCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data) (oldStep : Program 4),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  InternalOriginalUniformApplicationStepSelection.LeafCalibrated n arity oldStep →
  Calibrated n arity data oldStep

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.Targets
