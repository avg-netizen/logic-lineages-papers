module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open NumberedLeastCodeRepresentative
open InternalOriginalUniformDescentSelection (Data)
open InternalOriginalUniformVertexPath
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- ONE original vertex AST after n/arity, before every window and Gamma.
Its raw global function and every encoded source slice are calibrated,
including every malformed or rejected vertex input. No closure premise. -/
def ActualOriginalUniformVertexProgram : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat), ∃ oldVertex : Program 5,
    OldVertexCalibrated n arity oldVertex ∧
      ∀ (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
        VertexCalibratedAt n arity symbols S Gamma table oldVertex

/-- The SAME globally calibrated Data and old vertex work before windows.
The literal dispatched vertex and original path mapper preserve their full
numeric functions on every encoded source parameter slice. Typed activation
identifies actualJ only on its active inputs; every other input uses oldVertex. -/
def ActualOriginalUniformVertexPathCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data) (oldVertex : Program 5),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  OldVertexCalibrated n arity oldVertex →
  SelectedCalibrated n arity data oldVertex

/-- Actual original arrow construction exposes precisely both selected
typed graphs. The parameter, types and vertices remain symbolic. -/
def ActualParameterizedVertexActivation : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (α : Type) (Delta : List (Formula α))
    (parameter domain codomain argument value arrow : OTerm α),
  Nonempty (Derivation body Delta
    ((graph2 InternalListCodec.consCode arrow domain codomain).imp
      ((activationAccepted data parameter domain codomain argument value).iff
        (activationFactors data parameter domain argument value arrow))))

/-- Both literal dispatch branches hold internally. Active output is the
unchanged actualJ graph, with N(RAWargument) retained inside it. Inactive
output is the complete supplied old vertex graph at all unchanged inputs. -/
def ActualParameterizedVertexDispatch : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (oldVertex : Program 5)
    (α : Type) (Delta : List (Formula α))
    (out parameter domain codomain argument value : OTerm α),
  Nonempty (Derivation body Delta
    ((activationAccepted data parameter domain codomain argument value).imp
      ((vertexGraph data oldVertex out parameter domain codomain argument value).iff
        (InternalParameterizedCanonicalResultFold.applicationGraph
          data out domain codomain value argument parameter)))) ∧
  Nonempty (Derivation body Delta
    ((activationGraph data OrdinaryArithmetic.zeroTerm parameter domain codomain argument value).imp
      ((vertexGraph data oldVertex out parameter domain codomain argument value).iff
        (oldVertexGraph oldVertex out parameter domain codomain argument value))))

/-- Exact local invariant factorization under the actual arrow graph. No
old typed predicate, semantic typing or fold fixedness condition is inserted. -/
def ActualParameterizedVertexInvariantFactors : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (α : Type) (Delta : List (Formula α))
    (parameter domain codomain argument value arrow : OTerm α),
  Nonempty (Derivation body Delta
    ((graph2 InternalListCodec.consCode arrow domain codomain).imp
      ((invariantAccepted data parameter domain codomain argument value).iff
        (invariantFactors data parameter domain codomain argument value arrow))))

/-- Derive the exact local invariant premise of the existing path API from
the SAME quotient checker's typed propagation. No local preservation rule,
calibration, source decoding or target typing is supplied. -/
def ActualParameterizedVertexInvariantPreservation : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (oldStep : Program 4),
  InternalParameterizedApplicationPathLift.InvariantPreservation body
    (InternalParameterizedQuotientEdgeChecker.checker data oldStep) (invariant data)

/-- Discharge the exact existing single-edge compatibility premise using
the actual local invariant, both dispatched vertex outputs, and unchanged
edgeLift. ActualJ is only exposed under activation; all arguments stay raw. -/
def ActualParameterizedVertexEdgeCompatibility : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (oldStep : Program 4) (oldVertex : Program 5),
  InternalParameterizedApplicationPathLift.EdgeCompatibility body
    (InternalParameterizedQuotientEdgeChecker.checker data oldStep)
    (vertex data oldVertex) (invariant data)

/-- Concrete reflexive path transport at arbitrary symbolic p, with both
local arithmetic rules proved rather than supplied. The same actual mapper,
certificate, Data, raw argument and computed vertex outputs are retained. -/
def ActualParameterizedConcreteReflexivePathLift : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (oldStep : Program 4) (oldVertex : Program 5)
    (α : Type) (Delta : List (Formula α)) (ps : InternalParameterizedApplicationPathLift.Parameters α)
    (x y code out other mapped : OTerm α),
  Nonempty (Derivation body Delta
    (InternalParameterizedApplicationPathLift.inputs
      (InternalParameterizedQuotientEdgeChecker.checker data oldStep)
      (vertex data oldVertex) (invariant data) false ps x y code out other mapped)) →
  Nonempty (Derivation body Delta
    (InternalParameterizedPathChecker.pathGraph
      (InternalParameterizedQuotientEdgeChecker.checker data oldStep) out other mapped (ps 0)))

/-- The literal original positive checker and mapper, specialized to the
constructed programs. Neither invariant propagation nor edge compatibility
is a premise; the explicit local starting invariant remains an input graph. -/
def ActualParameterizedConcretePositivePathLift : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (oldStep : Program 4) (oldVertex : Program 5)
    (α : Type) (Delta : List (Formula α)) (ps : InternalParameterizedApplicationPathLift.Parameters α)
    (x y code out other mapped : OTerm α),
  Nonempty (Derivation body Delta
    (InternalParameterizedApplicationPathLift.inputs
      (InternalParameterizedQuotientEdgeChecker.checker data oldStep)
      (vertex data oldVertex) (invariant data) true ps x y code out other mapped)) →
  Nonempty (Derivation body Delta
    (InternalParameterizedPathChecker.positiveGraph
      (InternalParameterizedQuotientEdgeChecker.checker data oldStep) out other mapped (ps 0)))

/-- At original closed source types, the normalized SAME Data derives the
initial invariant from both typed premises and an actual parameter-pair
graph. Gamma's code stays symbolic; no codomain-membership or decode premise. -/
def ActualOriginalUniformInitialVertexInvariant : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun typ => typ ∈ S) →
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α)) (sigma tau : Ty)
    (parameter gammaCode argument value : OTerm α),
  Nonempty (Derivation body Delta
    ((initialPremises (OrdinaryArithmeticQuotient.contextCode symbols S table)
      (InternalOriginalUniformContextMembership.normalizeData data) sigma tau
      parameter gammaCode argument value).imp
      (invariantAccepted (InternalOriginalUniformContextMembership.normalizeData data)
        parameter (numeral (typeNumber sigma)) (numeral (typeNumber tau)) argument value)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathTargets
