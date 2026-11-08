module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatchDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatchTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalCanonicalFixedWindowVertexDispatch
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Exact original vertex equality on the active natural inputs. Original
leaf calibration and subtype closure suffice: canonical typed witnesses and
R_old(argument)=argument must be DERIVED externally, using the original typed
carrier and representative facts. Actual N calibration then removes the
argument normalization externally. No N-fixed premise is added internally. -/
def ActualOriginalCanonicalFixedWindowActiveVertexEquality : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data),
  SubtypeClosed (fun typ => typ ∈ S) →
  InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data →
  ∀ (context domain codomain argument value : Nat),
  Active (OrdinaryArithmeticQuotient.contextCode symbols S table) data
    context domain codomain argument value →
  evaluate (InternalCanonicalQuotientEdgeApplicationLift.actualJ data)
      (List.Vector.ofFn ![domain,codomain,value,argument]) =
    ApplicationCertificateLiftPath.vertex n arity Gamma
      context domain codomain argument value

/-- The ORIGINAL VertexCalibrated contract on EVERY five-vector, including
zero, malformed inputs, nonuniverse values, other windows and rejected guards.
The complete old vertex remains literally the inactive branch. Gamma is fixed
in calibration; the runtime window is contextCode symbols S table. -/
def ActualOriginalCanonicalFixedWindowVertexCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (data : Data) (oldVertex : Program 5),
  SubtypeClosed (fun typ => typ ∈ S) →
  InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data →
  InternalApplicationPathMap.VertexCalibrated n arity Gamma oldVertex →
  InternalApplicationPathMap.VertexCalibrated n arity Gamma
    (vertex (OrdinaryArithmeticQuotient.contextCode symbols S table) data oldVertex)

/-- Genuine internal factorization under the actual arrow-constructor graph.
Arbitrary leaves, window, body, variable type, context and symbolic terms are
allowed. No calibration or externally true typing is an internal premise. -/
def ActualInternalCanonicalFixedWindowVertexActivation : Prop :=
  ∀ (window : Nat) (data : Data) (body : Positive (Fin 1))
    (α : Type) (Delta : List (Formula α))
    (context domain codomain argument value arrow : OTerm α),
  Nonempty (Derivation body Delta
    ((graph2 InternalListCodec.consCode arrow domain codomain).imp
      ((activationAccepted window data context domain codomain argument value).iff
        (activationFactors window data context domain argument value arrow))))

/-- The active dispatched graph is iff the EXACT actualJ graph. N(argument)
stays inside actualJ. Neither an argument fixedness equation, old typed test,
good-run graph, output canonicality nor a representative law is supplied. -/
def ActualInternalCanonicalFixedWindowActiveVertexGraph : Prop :=
  ∀ (window : Nat) (data : Data) (oldVertex : Program 5)
    (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (context domain codomain argument value out : OTerm α),
  Nonempty (Derivation body Delta
    ((activationAccepted window data context domain codomain argument value).imp
      ((vertexGraph window data oldVertex out context domain codomain argument value).iff
        (applicationGraph data out domain codomain value argument))))

/-- The concrete invariant is EXACTLY the fixed context/domain/codomain
coordinates and both canonical typed graphs at the original closed types.
There are no hidden H, N-fixed, edge or path-acceptance factors. -/
def ActualInternalCanonicalFixedWindowInvariantFactors : Prop :=
  ∀ (window : Nat) (data : Data) (sigma tau : Ty)
    (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (context domain codomain argument value : OTerm α),
  Nonempty (Derivation body Delta
    ((invariantAccepted window data sigma tau context domain codomain argument value).iff
      (invariantFactors window data sigma tau context domain codomain argument value)))

/-- Closed type-code computation and the invariant coordinate equalities
derive the ACTUAL activation graph. No supplied arrow witness or external
calibration is required. The original symbolic coordinates remain visible. -/
def ActualInternalCanonicalFixedWindowInvariantActivation : Prop :=
  ∀ (window : Nat) (data : Data) (sigma tau : Ty)
    (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (context domain codomain argument value : OTerm α),
  Nonempty (Derivation body Delta
    ((invariantAccepted window data sigma tau context domain codomain argument value).imp
      (activationAccepted window data context domain codomain argument value)))

/-- Discharge the existing path API's exact local invariant premise at the
SAME selected canonical Edge, using its checked typed propagation. Only the
function value moves; all four path parameters and argument typing persist.
No target typedness, leaf calibration or invariant-preservation premise. -/
def ActualInternalCanonicalFixedWindowInvariantPreservation : Prop :=
  ∀ (window : Nat) (data : Data) (body : Positive (Fin 1)) (sigma tau : Ty),
  InternalApplicationPathLift.InvariantPreservation body
    (InternalCanonicalQuotientEdgeSelection.edgeChecker data)
    (invariant window data sigma tau)

/-- ONE shared canonical Data and ONE old vertex precede all bodies, types,
variable types, contexts and terms. Retain original and selected Edge/typed
calibration plus canonical Edge laws, and add both full vertex calibrations,
the exact dispatch laws and the concrete path invariant's local preservation.
No same-edge application compatibility or path lift is asserted here. -/
def ActualOriginalCanonicalFixedWindowVertexSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun typ => typ ∈ S) →
  ∃ data : Data, ∃ oldVertex : Program 5,
    InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data ∧
      (InternalCanonicalQuotientEdgeSelection.SelectedCalibrated
          n arity symbols S Gamma table data ∧
        (InternalCanonicalQuotientEdgeSelection.InternalLaws data ∧
          (InternalApplicationPathMap.VertexCalibrated n arity Gamma oldVertex ∧
            (InternalApplicationPathMap.VertexCalibrated n arity Gamma
                (vertex (OrdinaryArithmeticQuotient.contextCode symbols S table) data oldVertex) ∧
              (InternalLaws (OrdinaryArithmeticQuotient.contextCode symbols S table) data oldVertex ∧
                InvariantLaws (OrdinaryArithmeticQuotient.contextCode symbols S table) data)))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatchTargets
