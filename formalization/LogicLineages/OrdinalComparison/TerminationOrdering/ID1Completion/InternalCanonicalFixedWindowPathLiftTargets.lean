module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowPathLiftDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowPathLiftTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open InternalCanonicalFixedWindowVertexDispatch
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Discharge the EXISTING exact one-edge compatibility contract. Only the
checked application rule's external member calibration and subtype closure
remain. Source invariant propagation derives the target invariant/activation;
both actual vertex outputs become actualJ graphs, and the invariant's closed
type-coordinate equalities transport the original edgeLift graph. No target
typedness, N-fixedness, local compatibility or semantic object premise. -/
def ActualInternalCanonicalFixedWindowEdgeCompatibility : Prop :=
  ∀ (S : List Ty) (data : InternalCanonicalFixedWindowPathLift.Data),
  InternalStructuralEndpointGuard.MembershipCalibrated S data.member →
  SubtypeClosed (fun typ => typ ∈ S) →
  ∀ (window : Nat) (oldVertex : Program 5) (body : Positive (Fin 1)) (sigma tau : Ty),
  InternalApplicationPathLift.EdgeCompatibility body
    (InternalCanonicalQuotientEdgeSelection.edgeChecker data)
    (vertex window data oldVertex) (invariant window data sigma tau)

/-- Exact specialization of actualInternalReflexivePathLift, with its local
premises DISCHARGED rather than assumed. The source invariant, original path
certificate, both actual vertex outputs and actual original-map output remain
in the unchanged generic inputs. Arbitrary derivation contexts are retained. -/
def ActualInternalCanonicalFixedWindowReflexivePathLift : Prop :=
  ∀ (S : List Ty) (data : InternalCanonicalFixedWindowPathLift.Data),
  InternalStructuralEndpointGuard.MembershipCalibrated S data.member →
  SubtypeClosed (fun typ => typ ∈ S) →
  ∀ (window : Nat) (oldVertex : Program 5) (body : Positive (Fin 1)) (sigma tau : Ty)
    (α : Type) (Delta : List (Formula α)) (ps : InternalApplicationPathLift.Parameters α)
    (x y certificate out other mapped : OTerm α),
  Nonempty (Derivation body Delta
    (InternalApplicationPathLift.inputs
      (InternalCanonicalQuotientEdgeSelection.edgeChecker data)
      (vertex window data oldVertex) (invariant window data sigma tau)
      false ps x y certificate out other mapped)) →
  Nonempty (Derivation body Delta
    (InternalPathChecker.pathGraph
      (InternalCanonicalQuotientEdgeSelection.edgeChecker data) out other mapped))

/-- Exact specialization of actualInternalPositivePathLift at the SAME Edge,
vertex, invariant and original mapper. The positive checker still rejects nil.
No newly chosen path certificate/output, externally true path, target invariant,
semantic lift law or context-uniform object checker is a premise. -/
def ActualInternalCanonicalFixedWindowPositivePathLift : Prop :=
  ∀ (S : List Ty) (data : InternalCanonicalFixedWindowPathLift.Data),
  InternalStructuralEndpointGuard.MembershipCalibrated S data.member →
  SubtypeClosed (fun typ => typ ∈ S) →
  ∀ (window : Nat) (oldVertex : Program 5) (body : Positive (Fin 1)) (sigma tau : Ty)
    (α : Type) (Delta : List (Formula α)) (ps : InternalApplicationPathLift.Parameters α)
    (x y certificate out other mapped : OTerm α),
  Nonempty (Derivation body Delta
    (InternalApplicationPathLift.inputs
      (InternalCanonicalQuotientEdgeSelection.edgeChecker data)
      (vertex window data oldVertex) (invariant window data sigma tau)
      true ps x y certificate out other mapped)) →
  Nonempty (Derivation body Delta
    (InternalPathChecker.positiveGraph
      (InternalCanonicalQuotientEdgeSelection.edgeChecker data) out other mapped))

/-- ALL-input calibration follows by applying the EXISTING
InternalApplicationPathMapEvaluationProof.actualOriginalPathCalibration to
the dispatched vertex's original VertexCalibrated contract. Keep the exact
raw-list map, pair-coded entries and original edgeLift on RAW argument. -/
def ActualOriginalCanonicalFixedWindowLiftPathCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (data : InternalCanonicalFixedWindowPathLift.Data) (oldVertex : Program 5),
  SubtypeClosed (fun typ => typ ∈ S) →
  InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data →
  InternalApplicationPathMap.VertexCalibrated n arity Gamma oldVertex →
  InternalCanonicalFixedWindowPathLift.LiftPathCalibrated n arity Gamma
    (vertex (OrdinaryArithmeticQuotient.contextCode symbols S table) data oldVertex)

/-- Preserve the ORIGINAL outer pathValue on arguments that decode to this
fixed Gamma, with arbitrary raw payload and all other natural coordinates.
No new wrapper AST is defined. Malformed objects and different decoded Gammas
are deliberately not claimed by this fixed-Gamma bridge. -/
def ActualOriginalCanonicalFixedWindowDecodedPathValue : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (data : InternalCanonicalFixedWindowPathLift.Data) (oldVertex : Program 5),
  SubtypeClosed (fun typ => typ ∈ S) →
  InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data →
  InternalApplicationPathMap.VertexCalibrated n arity Gamma oldVertex →
  InternalCanonicalFixedWindowPathLift.PathValueOnDecodedArgument n arity Gamma
    (vertex (OrdinaryArithmeticQuotient.contextCode symbols S table) data oldVertex)

/-- ONE shared canonical Data and ONE old vertex precede EVERY closed type,
body, variable type, derivation context and symbolic term. Preserve original
leaf/Edge/typed/actualJ calibration and laws, both full vertex calibrations,
dispatch and invariant laws; add exact original path calibration, its decoded
fixed-Gamma wrapper equation and internal SAME-checker path transport.
This is not an object/context-uniform CertifiedApplicationLift or full ID1. -/
def ActualOriginalSelectedCanonicalFixedWindowPathLift : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun typ => typ ∈ S) →
  ∃ data : InternalCanonicalFixedWindowPathLift.Data, ∃ oldVertex : Program 5,
    InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data ∧
    InternalCanonicalQuotientEdgeSelection.SelectedCalibrated n arity symbols S Gamma table data ∧
    InternalCanonicalQuotientEdgeApplicationLift.ApplicationCalibrated n arity symbols S Gamma data ∧
    InternalCanonicalQuotientEdgeSelection.InternalLaws data ∧
    InternalCanonicalQuotientEdgeApplicationLift.InternalLaws data ∧
    InternalApplicationPathMap.VertexCalibrated n arity Gamma oldVertex ∧
    InternalApplicationPathMap.VertexCalibrated n arity Gamma
      (vertex (OrdinaryArithmeticQuotient.contextCode symbols S table) data oldVertex) ∧
    InternalCanonicalFixedWindowPathLift.LiftPathCalibrated n arity Gamma
      (vertex (OrdinaryArithmeticQuotient.contextCode symbols S table) data oldVertex) ∧
    InternalCanonicalFixedWindowPathLift.PathValueOnDecodedArgument n arity Gamma
      (vertex (OrdinaryArithmeticQuotient.contextCode symbols S table) data oldVertex) ∧
    InternalCanonicalFixedWindowVertexDispatch.InternalLaws
      (OrdinaryArithmeticQuotient.contextCode symbols S table) data oldVertex ∧
    InternalCanonicalFixedWindowVertexDispatch.InvariantLaws
      (OrdinaryArithmeticQuotient.contextCode symbols S table) data ∧
    InternalCanonicalFixedWindowPathLift.InternalLaws
      (OrdinaryArithmeticQuotient.contextCode symbols S table) data oldVertex

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowPathLiftTargets
