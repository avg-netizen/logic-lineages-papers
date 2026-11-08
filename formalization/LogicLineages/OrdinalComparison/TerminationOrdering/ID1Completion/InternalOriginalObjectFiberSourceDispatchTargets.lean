module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatchDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatchTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open InternalOriginalObjectFiberSourceDispatch
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The concrete left/constant-one/left-of-right/cons ASTs calibrate to the
UNCHANGED original gamma extractor, diagonal object guard, raw tag and arrow
code on every natural input. Totality of the original Object codec is used
externally; no opaque gamma/tag witness or internal reflection is supplied. -/
def ActualOriginalObjectSourceAuxiliaryCalibration : Prop :=
  (∀ xs : List.Vector Nat 1, evaluate gamma xs = GammaGuardCalibration.gammaValue xs) ∧
  (∀ xs : List.Vector Nat 1, evaluate valid xs = GammaGuardCalibration.objectValid (xs.get 0)) ∧
  (∀ xs : List.Vector Nat 2, evaluate tag xs = GuardCalibration.typeTagValue xs) ∧
  (∀ xs : List.Vector Nat 2, evaluate arrow xs = ApplicationDomain.arrowValue xs)

/-- The complete PATH checker, unchanged raw certificate, exact Boolean
activation and untouched four-input fallback, on all natural vectors. -/
def ActualOriginalObjectSourcePositiveEvaluation : Prop :=
  ∀ (window : Nat) (Gamma : List Ty) (data : Data) (oldPositive : Program 4)
    (xs : List.Vector Nat 4),
  (evaluate (positiveActivation window Gamma) xs =
      if xs.get 0 = window ∧
        ((Nat.unpair (xs.get 1)).1 = Encodable.encode Gamma ∧
          (Nat.unpair (xs.get 2)).1 = Encodable.encode Gamma) then 1 else 0) ∧
  (evaluate (positive window Gamma data oldPositive) xs =
      if xs.get 0 = window ∧
        ((Nat.unpair (xs.get 1)).1 = Encodable.encode Gamma ∧
          (Nat.unpair (xs.get 2)).1 = Encodable.encode Gamma) then
        evaluate (InternalPathChecker.checker
          (InternalCanonicalQuotientEdgeSelection.edgeChecker data) true)
          (List.Vector.ofFn ![(Nat.unpair (xs.get 1)).2,(Nat.unpair (xs.get 2)).2,xs.get 3])
      else evaluate oldPositive xs)

/-- The requested type stays in coordinate one and the raw payload is
canonical typed input zero. Off-window/off-fiber the full old vector survives. -/
def ActualOriginalObjectSourceTypedEvaluation : Prop :=
  ∀ (window : Nat) (Gamma : List Ty) (data : Data) (oldTyped : Program 3)
    (xs : List.Vector Nat 3),
  (evaluate (typedActivation window Gamma) xs =
      if xs.get 0 = window ∧ (Nat.unpair (xs.get 2)).1 = Encodable.encode Gamma then 1 else 0) ∧
  (evaluate (typed window Gamma data oldTyped) xs =
      if xs.get 0 = window ∧ (Nat.unpair (xs.get 2)).1 = Encodable.encode Gamma then
        evaluate (InternalCanonicalDescentSelection.selectedTyped data)
          (List.Vector.ofFn ![(Nat.unpair (xs.get 2)).2,xs.get 1])
      else evaluate oldTyped xs)

/-- BOTH fibers plus canonical context/function/argument typing activate
the original object pair around actualJ. All other inputs retain oldResult
itself, including literal original failure zero rather than pair(Gamma,0). -/
def ActualOriginalObjectSourceResultEvaluation : Prop :=
  ∀ (window : Nat) (Gamma : List Ty) (data : Data) (oldResult : Program 5)
    (xs : List.Vector Nat 5),
  (evaluate (resultActivation window Gamma data) xs =
      if (Nat.unpair (xs.get 3)).1 = Encodable.encode Gamma ∧
        ((Nat.unpair (xs.get 4)).1 = Encodable.encode Gamma ∧
          (xs.get 0 = window ∧
            (evaluate (InternalCanonicalDescentSelection.selectedTyped data)
                (List.Vector.ofFn ![(Nat.unpair (xs.get 3)).2,
                  InternalCanonicalFixedWindowVertexDispatch.arrowCode (xs.get 1) (xs.get 2)]) = 1 ∧
              evaluate (InternalCanonicalDescentSelection.selectedTyped data)
                (List.Vector.ofFn ![(Nat.unpair (xs.get 4)).2,xs.get 1]) = 1))) then 1 else 0) ∧
  (evaluate (result window Gamma data oldResult) xs =
      if (Nat.unpair (xs.get 3)).1 = Encodable.encode Gamma ∧
        ((Nat.unpair (xs.get 4)).1 = Encodable.encode Gamma ∧
          (xs.get 0 = window ∧
            (evaluate (InternalCanonicalDescentSelection.selectedTyped data)
                (List.Vector.ofFn ![(Nat.unpair (xs.get 3)).2,
                  InternalCanonicalFixedWindowVertexDispatch.arrowCode (xs.get 1) (xs.get 2)]) = 1 ∧
              evaluate (InternalCanonicalDescentSelection.selectedTyped data)
                (List.Vector.ofFn ![(Nat.unpair (xs.get 4)).2,xs.get 1]) = 1))) then
        Nat.pair (Encodable.encode Gamma)
          (evaluate (InternalCanonicalQuotientEdgeApplicationLift.actualJ data)
            (List.Vector.ofFn ![xs.get 1,xs.get 2,
              (Nat.unpair (xs.get 3)).2,(Nat.unpair (xs.get 4)).2]))
      else evaluate oldResult xs)

/-- ALL original four-vectors, with no validity, typing, fiber, window or
path-acceptance premise. Positive calibration is against original positiveValue,
not the quotient-edge checker. Every off-fiber/window default is preserved. -/
def ActualOriginalObjectSourcePositiveCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data) (oldPositive : Program 4),
  SubtypeClosed (fun typ => typ ∈ S) →
  InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data →
  PositiveCalibrated n arity oldPositive →
  PositiveCalibrated n arity
    (positive (OrdinaryArithmeticQuotient.contextCode symbols S table) Gamma data oldPositive)

/-- ALL original [context,type,object] vectors, at the SAME canonical Data.
The old global typed program supplies all inactive contexts and fibers. -/
def ActualOriginalObjectSourceTypedCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data) (oldTyped : Program 3),
  SubtypeClosed (fun typ => typ ∈ S) →
  InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data →
  TypedCalibrated n arity oldTyped →
  TypedCalibrated n arity
    (typed (OrdinaryArithmeticQuotient.contextCode symbols S table) Gamma data oldTyped)

/-- External bridge proving active success BEFORE pairing the payload.
The original resultOption must be some of the exact pair, not merely have a
matching getD. This prevents conflating raw application default zero with a
successful original object result. No internal reflection follows. -/
def ActualOriginalObjectSourceActiveResult : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data),
  SubtypeClosed (fun typ => typ ∈ S) →
  InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data →
  ∀ (context domain codomain functionObject argumentObject : Nat),
  resultActive (OrdinaryArithmeticQuotient.contextCode symbols S table) Gamma data
    context domain codomain functionObject argumentObject →
  let xs := List.Vector.ofFn ![context,domain,codomain,functionObject,argumentObject]
  let out := Nat.pair (Encodable.encode Gamma)
    (evaluate (InternalCanonicalQuotientEdgeApplicationLift.actualJ data)
      (List.Vector.ofFn ![domain,codomain,
        (Nat.unpair functionObject).2,(Nat.unpair argumentObject).2]))
  ApplicationDomain.active n arity xs ∧
    (ApplicationResultBuilder.resultOption n arity xs = some out ∧
      ApplicationResultBuilder.resultValue n arity xs = out)

/-- Exact original TOTAL resultValue on EVERY natural five-vector. Typed
activation is part of the AST, not a premise restricting this calibration.
No replacement of off-domain, cross-Gamma or malformed-context behavior. -/
def ActualOriginalObjectSourceResultCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data) (oldResult : Program 5),
  SubtypeClosed (fun typ => typ ∈ S) →
  InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data →
  ResultCalibrated n arity oldResult →
  ResultCalibrated n arity
    (result (OrdinaryArithmeticQuotient.contextCode symbols S table) Gamma data oldResult)

/-- Arbitrary body, Delta, symbolic inputs and actual output. Only actual
unpair graphs and context equality are premises. The conclusion is the FULL
graph iff of the SAME whole-path checker, retaining the supplied certificate. -/
def ActualInternalOriginalObjectSourcePositiveGraph : Prop :=
  ∀ (window : Nat) (Gamma : List Ty) (data : Data) (oldPositive : Program 4)
    (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (context functionObject targetObject source target certificate out : OTerm α),
  Nonempty (Derivation body Delta
    ((positivePremises window Gamma context functionObject targetObject source target).imp
      ((programGraph (positive window Gamma data oldPositive) out
          (positiveArguments context functionObject targetObject certificate)).iff
        (graph3 (InternalPathChecker.checker
          (InternalCanonicalQuotientEdgeSelection.edgeChecker data) true)
          out source target certificate))))

/-- Exact active graph iff to T(payload,requestedType), for arbitrary
output and symbolic requested type. No externally true typedness is imported. -/
def ActualInternalOriginalObjectSourceTypedGraph : Prop :=
  ∀ (window : Nat) (Gamma : List Ty) (data : Data) (oldTyped : Program 3)
    (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (context typ object payload out : OTerm α),
  Nonempty (Derivation body Delta
    ((typedPremises window Gamma context object payload).imp
      ((programGraph (typed window Gamma data oldTyped) out
          (typedArguments context typ object)).iff
        (graph2 (InternalCanonicalDescentSelection.selectedTyped data) out payload typ))))

/-- Exact existential actualJ graph AND original pair-output graph.
The RAW argument remains inside actualJ with its internal N computation.
The output object is supplied, not reselected; no fixedness or old typed law. -/
def ActualInternalOriginalObjectSourceResultGraph : Prop :=
  ∀ (window : Nat) (Gamma : List Ty) (data : Data) (oldResult : Program 5)
    (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (context domain codomain functionObject argumentObject function argument out : OTerm α),
  Nonempty (Derivation body Delta
    ((resultPremises window Gamma data context domain codomain
        functionObject argumentObject function argument).imp
      ((programGraph (result window Gamma data oldResult) out
          (resultArguments context domain codomain functionObject argumentObject)).iff
        (pairedApplicationGraph Gamma data out domain codomain function argument))))

/-- The actual activation graph at ZERO yields iff with the literal old
program on the unchanged complete input tuple and unchanged supplied out. -/
def ActualInternalOriginalObjectSourcePositiveZeroGraph : Prop :=
  ∀ (window : Nat) (Gamma : List Ty) (data : Data) (oldPositive : Program 4),
  ZeroLaw (positiveActivation window Gamma) (positive window Gamma data oldPositive) oldPositive

/-- The actual activation graph at ZERO yields iff with the literal old
program on the unchanged complete input tuple and unchanged supplied out. -/
def ActualInternalOriginalObjectSourceTypedZeroGraph : Prop :=
  ∀ (window : Nat) (Gamma : List Ty) (data : Data) (oldTyped : Program 3),
  ZeroLaw (typedActivation window Gamma) (typed window Gamma data oldTyped) oldTyped

/-- The actual activation graph at ZERO yields iff with the literal old
program on the unchanged complete input tuple and unchanged supplied out. -/
def ActualInternalOriginalObjectSourceResultZeroGraph : Prop :=
  ∀ (window : Nat) (Gamma : List Ty) (data : Data) (oldResult : Program 5),
  ZeroLaw (resultActivation window Gamma data) (result window Gamma data oldResult) oldResult

/-- ONE canonical Data and globally calibrated oldSource, oldComp and
oldResult precede all bodies, types, contexts and terms. E, T and J use the
SAME leaves. These are source DISPATCH PRIMITIVES only, not a closed source
package, path lift, CertifiedApplicationLift or all-type downward theorem. -/
def ActualOriginalSelectedObjectSourceDispatch : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun typ => typ ∈ S) →
  ∃ data : Data, ∃ oldSource : SourcePresentation.Data,
  ∃ oldComp : JointGammaComputability.Data, ∃ oldResult : Program 5,
    InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data ∧
    InternalCanonicalQuotientEdgeSelection.SelectedCalibrated n arity symbols S Gamma table data ∧
    InternalCanonicalQuotientEdgeApplicationLift.ApplicationCalibrated n arity symbols S Gamma data ∧
    InternalCanonicalQuotientEdgeSelection.InternalLaws data ∧
    InternalCanonicalQuotientEdgeApplicationLift.InternalLaws data ∧
    ContextUniform.Calibrated oldSource n arity ∧
    JointGammaComputability.Calibrated oldComp n arity ∧
    ResultCalibrated n arity oldResult ∧
    ActualOriginalObjectSourceAuxiliaryCalibration ∧
    PositiveCalibrated n arity
      (positive (OrdinaryArithmeticQuotient.contextCode symbols S table) Gamma data oldSource.positive) ∧
    TypedCalibrated n arity
      (typed (OrdinaryArithmeticQuotient.contextCode symbols S table) Gamma data oldComp.typed) ∧
    ResultCalibrated n arity
      (result (OrdinaryArithmeticQuotient.contextCode symbols S table) Gamma data oldResult) ∧
    InternalOriginalObjectFiberSourceDispatch.InternalLaws
      (OrdinaryArithmeticQuotient.contextCode symbols S table) Gamma data
      oldSource.positive oldComp.typed oldResult

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatchTargets
