module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeTypeGuardDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeTypeGuardTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalQuotientEdgeTypeGuard
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- A semantic property of the UNCHANGED original numeric edge checker.
For a subtype-closed window, every accepted edge has both canonical endpoints
in the original typed carrier at the source endpoint's outer tag. The target
universe fact must be derived from original step soundness and preservation;
neither endpoint typing, successful decode, nor valid certificate is assumed. -/
def ActualOriginalQuotientEdgeTypedEndpoints : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun typ => typ ∈ S) →
  ∀ (x y certificate : Nat),
  NumberedNumericQuotientEdge.numericEdgeTest n arity symbols S Gamma table x y certificate = true →
    InternalOriginalTypedCarrier.typedValue n arity symbols S Gamma
      (List.Vector.ofFn ![x,(Nat.unpair x).1]) = 1 ∧
    InternalOriginalTypedCarrier.typedValue n arity symbols S Gamma
      (List.Vector.ofFn ![y,(Nat.unpair x).1]) = 1

/-- The wrapper preserves the ENTIRE original zero/one function on every
natural endpoint/certificate triple, including every rejecting or malformed
input and certificate zero. Subtype closure is essential to this contract.
ANY all-input-calibrated selected typed Program is allowed, so later wrappers
may expose additional internally useful but externally redundant guards. -/
def ActualOriginalQuotientEdgeTypedWrapperCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (data : InternalQuotientEdgeChecker.Data) (typedProgram : Program 2),
  SubtypeClosed (fun typ => typ ∈ S) →
  InternalQuotientEdgeChecker.Calibrated n arity symbols S Gamma table data →
  InternalOriginalTypedCarrier.Calibrated n arity symbols S Gamma typedProgram →
  ∀ v : List.Vector Nat 3,
    evaluate (checker data typedProgram) v =
      (NumberedNumericQuotientEdge.numericEdgeTest n arity symbols S Gamma table
        (v.get 0) (v.get 1) (v.get 2)).toNat

/-- Internal decomposition AND reconstruction from the actual source-tag
graph. This is uniform in arbitrary Program leaves and symbolic terms, with
no calibration, subtype closure, semantic decode or target-typing premise. -/
def ActualOriginalQuotientEdgeTypedAcceptanceEquation : Prop :=
  ∀ (body : Positive (Fin 1)) (data : InternalQuotientEdgeChecker.Data)
    (typedProgram : Program 2) (α : Type) (x y certificate typ : OTerm α),
  Nonempty (Derivation body []
    ((sourceTypeGraph typ x).imp
      ((accepted data typedProgram x y certificate).iff
        (requirements data typedProgram x y certificate typ))))

/-- Acceptance plus an actual source-tag graph exposes the SAME SELECTED
typed Program on BOTH endpoints at that symbolic type. This is the intended
local invariant consumer; it does not assume or derive full-context dispatch,
representative congruence, source computability, or application lifting. -/
def ActualOriginalQuotientEdgeTypedTransport : Prop :=
  ∀ (body : Positive (Fin 1)) (data : InternalQuotientEdgeChecker.Data)
    (typedProgram : Program 2) (α : Type) (x y certificate typ : OTerm α),
  Nonempty (Derivation body []
    ((accepted data typedProgram x y certificate).imp
      ((sourceTypeGraph typ x).imp
        (typed typedProgram x typ ⊓ typed typedProgram y typ))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeTypeGuardTargets
