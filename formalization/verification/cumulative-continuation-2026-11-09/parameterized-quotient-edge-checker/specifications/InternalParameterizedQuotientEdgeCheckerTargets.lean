module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalParameterizedQuotientEdgeChecker
open InternalOriginalUniformDescentSelection (Data)
open InternalOriginalUniformParameterLeaves (parameterCode)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The same globally calibrated Data and old step precede every window
and Gamma. All raw endpoints and certificates retain the original zero/one
function. Subtype closure justifies W's additional raw-target source validity. -/
def ActualOriginalParameterizedQuotientCoreCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data) (oldStep : Program 4),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  InternalOriginalUniformApplicationStepSelection.LeafCalibrated n arity oldStep →
  ∀ (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun typ => typ ∈ S) →
  ∀ v : List.Vector Nat 3,
  evaluate (coreChecker data oldStep) (List.Vector.ofFn
      ![v.get 0,v.get 1,v.get 2,parameterCode symbols S Gamma table]) =
    (NumberedNumericQuotientEdge.numericEdgeTest n arity symbols S Gamma table
      (v.get 0) (v.get 1) (v.get 2)).toNat

/-- Both canonical typed guards are redundant on original accepted edges.
Rejecting, malformed and zero certificates remain covered; the target
representative still has no source-universe filter on any input. -/
def ActualOriginalParameterizedTypedQuotientCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data) (oldStep : Program 4),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  InternalOriginalUniformApplicationStepSelection.LeafCalibrated n arity oldStep →
  ∀ (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun typ => typ ∈ S) →
  ∀ v : List.Vector Nat 3,
  evaluate (checker data oldStep) (List.Vector.ofFn
      ![v.get 0,v.get 1,v.get 2,parameterCode symbols S Gamma table]) =
    (NumberedNumericQuotientEdge.numericEdgeTest n arity symbols S Gamma table
      (v.get 0) (v.get 1) (v.get 2)).toNat

/-- Literal selector-based decomposition and reconstruction in the original
calculus. All arithmetic terms, including p, are symbolic; no calibration,
decoded certificate, endpoint typing or semantic premise occurs. -/
def ActualParameterizedQuotientAcceptance : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (oldStep : Program 4)
    (α : Type) (Delta : List (Formula α))
    (x y certificate rawSource rawTarget rawStep parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((selectors certificate rawSource rawTarget rawStep).imp
      ((coreAccepted data oldStep x y certificate parameter).iff
        (requirements data oldStep x y rawSource rawTarget rawStep parameter))))

/-- Acceptance exposes the SAME actual N for both raw certificate endpoints.
The source-validity fact needed to remove only the source filter is derived
from W, rather than added as a premise. The converse reconstructs the filter. -/
def ActualParameterizedNormalizedQuotientAcceptance : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (oldStep : Program 4)
    (α : Type) (Delta : List (Formula α))
    (x y certificate rawSource rawTarget rawStep parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((selectors certificate rawSource rawTarget rawStep).imp
      ((coreAccepted data oldStep x y certificate parameter).iff
        (normalizedRequirements data oldStep x y rawSource rawTarget rawStep parameter))))

/-- The actual source tag graph determines both typed calls of the literal
wrapper. Neither target typing nor a separately supplied semantic type is
assumed; the same symbolic requested type occurs in both conclusions. -/
def ActualParameterizedTypedQuotientAcceptance : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (oldStep : Program 4)
    (α : Type) (Delta : List (Formula α))
    (x y certificate typ parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((sourceTypeGraph typ x).imp
      ((accepted data oldStep x y certificate parameter).iff
        (typedRequirements data oldStep x y certificate typ parameter))))

/-- Genuine local propagation for the SAME selected typed and quotient-edge
ASTs. The source tag graph follows from selected typing. No calibration,
subtype-closure, raw selector, target-typing or invariant-propagation premise. -/
def ActualParameterizedTypedQuotientPropagation : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (oldStep : Program 4)
    (α : Type) (Delta : List (Formula α))
    (x y certificate typ parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((typedAccepted data x typ parameter ⊓
      accepted data oldStep x y certificate parameter).imp
      (typedAccepted data y typ parameter)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerTargets
