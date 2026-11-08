module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatchDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowPathLift
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open InternalCanonicalFixedWindowVertexDispatch
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The SAME original leaves. This package adds no Program, path syntax,
certificate representation, proof field or semantic correctness field. -/
abbrev Data := InternalCanonicalDescentSelection.Data

/-- Exactly the existing original path-map calibration, on EVERY natural
five-vector [certificate,context,domain,codomain,RAW argument]. The selected
vertex fixes Gamma; the mapper retains the original entryEdge and edgeLift. -/
def LiftPathCalibrated (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (vertexProgram : Program 5) : Prop :=
  ∀ v : List.Vector Nat 5,
    evaluate (InternalApplicationPathMap.pathMap vertexProgram) v =
      ApplicationCertificateLiftPath.liftPath n arity Gamma
        (v.get 1) (v.get 2) (v.get 3) (v.get 4) (v.get 0)

/-- Only an EXTERNAL fixed-Gamma equation for the ORIGINAL pathValue wrapper.
The argument-object code is decoded once to its original Gamma and raw payload.
This is not a new wrapper Program, an internal decoding premise, a malformed-
object theorem or an all-context internal compiler. -/
def PathValueOnDecodedArgument (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (vertexProgram : Program 5) : Prop :=
  ∀ (context domain codomain argumentObject argument certificate : Nat),
    Encodable.decode (α := ContextUniform.Object) argumentObject = some (Gamma,argument) →
    evaluate (InternalApplicationPathMap.pathMap vertexProgram)
        (List.Vector.ofFn ![certificate,context,domain,codomain,argument]) =
      ApplicationCertificateLiftPath.pathValue n arity
        (List.Vector.ofFn ![context,domain,codomain,argumentObject,certificate])

/-- Properties of ONE fixed selection, not Data fields or supplied laws.
The edge, dispatched vertex, arithmetic invariant and generic inputs are used
VERBATIM. Only closed sigma/tau and the selected window are fixed; symbolic
path parameters, endpoints, certificate and all three outputs remain arbitrary.
There is no new path AST or alternate edge-transformer output. -/
def InternalLaws (window : Nat) (data : Data) (oldVertex : Program 5) : Prop :=
  ∀ (body : Positive (Fin 1)) (sigma tau : Ty),
    InternalApplicationPathLift.EdgeCompatibility body
      (InternalCanonicalQuotientEdgeSelection.edgeChecker data)
      (vertex window data oldVertex) (invariant window data sigma tau) ∧
    ∀ (α : Type) (Delta : List (Formula α)) (ps : InternalApplicationPathLift.Parameters α)
      (x y certificate out other mapped : OTerm α),
      (Nonempty (Derivation body Delta
          (InternalApplicationPathLift.inputs
            (InternalCanonicalQuotientEdgeSelection.edgeChecker data)
            (vertex window data oldVertex) (invariant window data sigma tau)
            false ps x y certificate out other mapped)) →
        Nonempty (Derivation body Delta
          (InternalPathChecker.pathGraph
            (InternalCanonicalQuotientEdgeSelection.edgeChecker data) out other mapped))) ∧
      (Nonempty (Derivation body Delta
          (InternalApplicationPathLift.inputs
            (InternalCanonicalQuotientEdgeSelection.edgeChecker data)
            (vertex window data oldVertex) (invariant window data sigma tau)
            true ps x y certificate out other mapped)) →
        Nonempty (Derivation body Delta
          (InternalPathChecker.positiveGraph
            (InternalCanonicalQuotientEdgeSelection.edgeChecker data) out other mapped)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowPathLift
