module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open SourceComputabilityFormulaSupportProof InternalOriginalObjectFiberPathDispatch
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The ORIGINAL Object codec is total on Nat. Its product encoding is the
actual Nat.pair, and its fixed-Gamma fiber is detected by the actual left
coordinate. This statement is external and supplies no internal reflection. -/
def ActualOriginalObjectFiberCodec : Prop :=
  (∀ code : Nat, ∃ obj : ContextUniform.Object, Encodable.decode code = some obj) ∧
  (∀ (Gamma : List Ty) (argument : Nat),
    ContextUniform.objectCode Gamma argument = Nat.pair (Encodable.encode Gamma) argument) ∧
  (∀ (Gamma : List Ty) (argumentObject : Nat),
    Encodable.decode (α := ContextUniform.Object) argumentObject =
        some (Gamma,(Nat.unpair argumentObject).2) ↔
      (Nat.unpair argumentObject).1 = Encodable.encode Gamma)

/-- Exact branch evaluation on ALL five natural inputs. The active input
order is deliberately different from the outer pathValue order. -/
def ActualOriginalObjectFiberDispatchEvaluation : Prop :=
  ∀ (Gamma : List Ty) (vertexProgram oldLift : Program 5) (xs : List.Vector Nat 5),
    evaluate (dispatch Gamma vertexProgram oldLift) xs =
      if (Nat.unpair (xs.get 3)).1 = Encodable.encode Gamma then
        evaluate (InternalApplicationPathMap.pathMap vertexProgram)
          (List.Vector.ofFn ![xs.get 4,xs.get 0,xs.get 1,xs.get 2,
            (Nat.unpair (xs.get 3)).2])
      else evaluate oldLift xs

/-- Exact all-input calibration to the UNCHANGED original total pathValue.
The active mapper is the SAME selected canonical fixed-window vertex. The
inactive oldLift retains all Gammas, all windows and all original defaults. -/
def ActualOriginalObjectFiberPathValueCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (data : InternalCanonicalFixedWindowPathLift.Data) (oldVertex oldLift : Program 5),
  SubtypeClosed (fun typ => typ ∈ S) →
  InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data →
  InternalApplicationPathMap.VertexCalibrated n arity Gamma oldVertex →
  PathValueCalibrated n arity oldLift →
  PathValueCalibrated n arity
    (dispatch Gamma
      (InternalCanonicalFixedWindowVertexDispatch.vertex
        (OrdinaryArithmeticQuotient.contextCode symbols S table) data oldVertex) oldLift)

/-- Internal generated-code inverse AND reverse reconstruction, at the
original object-code pair. The right payload is RAW and unconstrained. -/
def ActualInternalOriginalObjectFiberPairGraph : Prop :=
  ∀ (Gamma : List Ty) (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (argumentObject argument : OTerm α),
  Nonempty (Derivation body Delta
    ((graph2 InternalPairing.pairing argumentObject
        (numeral (Encodable.encode Gamma)) argument).iff
      (fiberCoordinates Gamma argumentObject argument)))

/-- Only actual left/right AST graphs are premises. The left output is the
fixed encoded Gamma numeral; the actual supplied out is preserved exactly. -/
def ActualInternalOriginalObjectFiberActiveGraph : Prop :=
  ∀ (Gamma : List Ty) (vertexProgram oldLift : Program 5)
    (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (context domain codomain argumentObject argument certificate out : OTerm α),
  Nonempty (Derivation body Delta
    ((fiberCoordinates Gamma argumentObject argument).imp
      ((dispatchGraph Gamma vertexProgram oldLift
          out context domain codomain argumentObject certificate).iff
        (InternalApplicationPathMap.mapGraph vertexProgram
          out certificate context domain codomain argument))))

/-- The actual zero-output test graph forces the untouched oldLift branch.
This does not replace a failed object/context decoder by a new default. -/
def ActualInternalOriginalObjectFiberZeroGraph : Prop :=
  ∀ (Gamma : List Ty) (vertexProgram oldLift : Program 5)
    (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (context domain codomain argumentObject certificate out : OTerm α),
  Nonempty (Derivation body Delta
    ((fiberTestGraph Gamma OrdinaryArithmetic.zeroTerm
        context domain codomain argumentObject certificate).imp
      ((dispatchGraph Gamma vertexProgram oldLift
          out context domain codomain argumentObject certificate).iff
        (oldLiftGraph oldLift out context domain codomain argumentObject certificate))))

/-- Nonmatch is object-language inequality at the actual left-coordinate
graph. No standard-model decoding/evaluation claim is an internal premise. -/
def ActualInternalOriginalObjectFiberNonmatchGraph : Prop :=
  ∀ (Gamma : List Ty) (vertexProgram oldLift : Program 5)
    (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (context domain codomain argumentObject leftCode certificate out : OTerm α),
  Nonempty (Derivation body Delta
    (((graph1 InternalUnpair.left leftCode argumentObject) ⊓
        (InternalControlGraph.equal leftCode (numeral (Encodable.encode Gamma))).not).imp
      ((dispatchGraph Gamma vertexProgram oldLift
          out context domain codomain argumentObject certificate).iff
        (oldLiftGraph oldLift out context domain codomain argumentObject certificate))))

/-- Select ONE canonical Data, ONE oldVertex and ONE globally calibrated
oldLift before ALL bodies, closed types, contexts and symbolic terms. Preserve
the SAME fixed-window path package and add the original object-fiber wrapper.
This does not select an internally useful mapper uniformly over Gamma. -/
def ActualOriginalSelectedObjectFiberPathDispatch : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun typ => typ ∈ S) →
  ∃ data : InternalCanonicalFixedWindowPathLift.Data,
  ∃ oldVertex : Program 5, ∃ oldLift : Program 5,
    InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data ∧
    InternalCanonicalQuotientEdgeSelection.SelectedCalibrated n arity symbols S Gamma table data ∧
    InternalCanonicalQuotientEdgeApplicationLift.ApplicationCalibrated n arity symbols S Gamma data ∧
    InternalCanonicalQuotientEdgeSelection.InternalLaws data ∧
    InternalCanonicalQuotientEdgeApplicationLift.InternalLaws data ∧
    InternalApplicationPathMap.VertexCalibrated n arity Gamma oldVertex ∧
    InternalApplicationPathMap.VertexCalibrated n arity Gamma
      (InternalCanonicalFixedWindowVertexDispatch.vertex
        (OrdinaryArithmeticQuotient.contextCode symbols S table) data oldVertex) ∧
    InternalCanonicalFixedWindowPathLift.LiftPathCalibrated n arity Gamma
      (InternalCanonicalFixedWindowVertexDispatch.vertex
        (OrdinaryArithmeticQuotient.contextCode symbols S table) data oldVertex) ∧
    InternalCanonicalFixedWindowPathLift.PathValueOnDecodedArgument n arity Gamma
      (InternalCanonicalFixedWindowVertexDispatch.vertex
        (OrdinaryArithmeticQuotient.contextCode symbols S table) data oldVertex) ∧
    InternalCanonicalFixedWindowVertexDispatch.InternalLaws
      (OrdinaryArithmeticQuotient.contextCode symbols S table) data oldVertex ∧
    InternalCanonicalFixedWindowVertexDispatch.InvariantLaws
      (OrdinaryArithmeticQuotient.contextCode symbols S table) data ∧
    InternalCanonicalFixedWindowPathLift.InternalLaws
      (OrdinaryArithmeticQuotient.contextCode symbols S table) data oldVertex ∧
    PathValueCalibrated n arity oldLift ∧
    PathValueCalibrated n arity
      (dispatch Gamma
        (InternalCanonicalFixedWindowVertexDispatch.vertex
          (OrdinaryArithmeticQuotient.contextCode symbols S table) data oldVertex) oldLift) ∧
    InternalOriginalObjectFiberPathDispatch.InternalLaws Gamma
      (InternalCanonicalFixedWindowVertexDispatch.vertex
        (OrdinaryArithmeticQuotient.contextCode symbols S table) data oldVertex) oldLift

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchTargets
