module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatchDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardCalibrationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationDomainDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaComputabilityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatch
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The SAME canonical leaves. No source closure, correctness, reflection,
path transport or certified-lift field is added. -/
abbrev Data := InternalCanonicalDescentSelection.Data

/-- Concrete auxiliaries for the ORIGINAL total Object codec, not opaque
program witnesses selected from extensional primitive recursiveness. -/
def gamma : Program 1 := InternalUnpair.left
def valid : Program 1 := InternalCanonicalFixedWindowVertexDispatch.constant 1 1
def tag : Program 2 := leftOf (rightOf (.projection 1))
def arrow : Program 2 := InternalListCodec.consCode

/-- Exact external all-input contracts; no success or validity restriction. -/
def PositiveCalibrated (n : Nat) (arity : Fin n → Nat) (p : Program 4) : Prop :=
  ∀ xs, evaluate p xs = ContextUniform.positiveValue n arity xs

def TypedCalibrated (n : Nat) (arity : Fin n → Nat) (p : Program 3) : Prop :=
  ∀ xs, evaluate p xs = JointGammaTyped.typedValue n arity xs

def ResultCalibrated (n : Nat) (arity : Fin n → Nat) (p : Program 5) : Prop :=
  ∀ xs, evaluate p xs = ApplicationResultBuilder.resultValue n arity xs

/-- Positive inputs are [context,functionObject,targetObject,PATH certificate].
There is no endpoint typing or edge-acceptance factor in this dispatch test. -/
def positiveActivation (window : Nat) (Gamma : List Ty) : Program 4 :=
  InternalAcceptance.conjunction
    (InternalApplicationStepPeel.same (.projection 0)
      (InternalCanonicalFixedWindowVertexDispatch.constant 4 window))
    (InternalAcceptance.conjunction
      (InternalApplicationStepPeel.same (leftOf (.projection 1))
        (InternalCanonicalFixedWindowVertexDispatch.constant 4 (Encodable.encode Gamma)))
      (InternalApplicationStepPeel.same (leftOf (.projection 2))
        (InternalCanonicalFixedWindowVertexDispatch.constant 4 (Encodable.encode Gamma))))

/-- This is the WHOLE original positive path checker over the SAME canonical
Edge. The raw list certificate is not passed to a single-edge checker. -/
def positiveBranch (data : Data) : Program 4 :=
  .composition (InternalPathChecker.checker
    (InternalCanonicalQuotientEdgeSelection.edgeChecker data) true)
    ![rightOf (.projection 1),rightOf (.projection 2),.projection 3]

def positive (window : Nat) (Gamma : List Ty) (data : Data) (oldPositive : Program 4) : Program 4 :=
  InternalAcceptance.branch (positiveActivation window Gamma) oldPositive (positiveBranch data)

/-- Typed inputs are [context,requestedType,object]. The canonical checker
receives [RAW right(object),requestedType], in that order. -/
def typedActivation (window : Nat) (Gamma : List Ty) : Program 3 :=
  InternalAcceptance.conjunction
    (InternalApplicationStepPeel.same (.projection 0)
      (InternalCanonicalFixedWindowVertexDispatch.constant 3 window))
    (InternalApplicationStepPeel.same (leftOf (.projection 2))
      (InternalCanonicalFixedWindowVertexDispatch.constant 3 (Encodable.encode Gamma)))

def typedBranch (data : Data) : Program 3 :=
  .composition (InternalCanonicalDescentSelection.selectedTyped data)
    ![rightOf (.projection 2),.projection 1]

def typed (window : Nat) (Gamma : List Ty) (data : Data) (oldTyped : Program 3) : Program 3 :=
  InternalAcceptance.branch (typedActivation window Gamma) oldTyped (typedBranch data)

/-- Result inputs are [context,domain,codomain,functionObject,argumentObject].
BOTH object fibers and the exact existing canonical typed vertex activation
are required. On invalid typing/window the old result, not pair(Gamma,0), wins. -/
def resultActivation (window : Nat) (Gamma : List Ty) (data : Data) : Program 5 :=
  InternalAcceptance.conjunction
    (InternalApplicationStepPeel.same (leftOf (.projection 3))
      (InternalCanonicalFixedWindowVertexDispatch.constant 5 (Encodable.encode Gamma)))
    (InternalAcceptance.conjunction
      (InternalApplicationStepPeel.same (leftOf (.projection 4))
        (InternalCanonicalFixedWindowVertexDispatch.constant 5 (Encodable.encode Gamma)))
      (.composition (InternalCanonicalFixedWindowVertexDispatch.activation window data)
        ![.projection 0,.projection 1,.projection 2,
          rightOf (.projection 4),rightOf (.projection 3)]))

/-- Actual J(domain,codomain,RAW right(function),RAW right(argument)).
J retains its own N(argument); the function is not normalized a second time. -/
def resultBranch (Gamma : List Ty) (data : Data) : Program 5 :=
  pairOf (InternalCanonicalFixedWindowVertexDispatch.constant 5 (Encodable.encode Gamma))
    (.composition (InternalCanonicalQuotientEdgeApplicationLift.actualJ data)
      ![.projection 1,.projection 2,rightOf (.projection 3),rightOf (.projection 4)])

def result (window : Nat) (Gamma : List Ty) (data : Data) (oldResult : Program 5) : Program 5 :=
  InternalAcceptance.branch (resultActivation window Gamma data) oldResult (resultBranch Gamma data)

def resultActive (window : Nat) (Gamma : List Ty) (data : Data)
    (context domain codomain functionObject argumentObject : Nat) : Prop :=
  (Nat.unpair functionObject).1 = Encodable.encode Gamma ∧
    ((Nat.unpair argumentObject).1 = Encodable.encode Gamma ∧
      InternalCanonicalFixedWindowVertexDispatch.Active window data
        context domain codomain (Nat.unpair argumentObject).2 (Nat.unpair functionObject).2)

def positiveArguments {α : Type} (context functionObject targetObject certificate : OTerm α) :
    Fin 4 → OTerm α :=
  Fin.cons context (Fin.cons functionObject (Fin.cons targetObject (Fin.cons certificate Fin.elim0)))

def typedArguments {α : Type} (context typ object : OTerm α) : Fin 3 → OTerm α :=
  Fin.cons context (Fin.cons typ (Fin.cons object Fin.elim0))

def resultArguments {α : Type} (context domain codomain functionObject argumentObject : OTerm α) :
    Fin 5 → OTerm α :=
  Fin.cons context (Fin.cons domain (Fin.cons codomain
    (Fin.cons functionObject (Fin.cons argumentObject Fin.elim0))))

/-- Only actual original unpair AST graphs occur here. Their right payload
is raw and unconstrained; no externally true decoder equation is reflected. -/
def objectCoordinates {α : Type} (Gamma : List Ty) (object payload : OTerm α) : Formula α :=
  graph1 InternalUnpair.left (numeral (Encodable.encode Gamma)) object ⊓
    graph1 InternalUnpair.right payload object

def positivePremises {α : Type} (window : Nat) (Gamma : List Ty)
    (context functionObject targetObject source target : OTerm α) : Formula α :=
  equal context (numeral window) ⊓
    (objectCoordinates Gamma functionObject source ⊓ objectCoordinates Gamma targetObject target)

def typedPremises {α : Type} (window : Nat) (Gamma : List Ty)
    (context object payload : OTerm α) : Formula α :=
  equal context (numeral window) ⊓ objectCoordinates Gamma object payload

/-- The result premise includes the EXACT canonical typed activation, in
vertex order [context,domain,codomain,RAW argument,RAW function]. -/
def resultPremises {α : Type} (window : Nat) (Gamma : List Ty) (data : Data)
    (context domain codomain functionObject argumentObject function argument : OTerm α) : Formula α :=
  objectCoordinates Gamma functionObject function ⊓
    (objectCoordinates Gamma argumentObject argument ⊓
      InternalCanonicalFixedWindowVertexDispatch.activationAccepted window data
        context domain codomain argument function)

/-- The result is the ORIGINAL pair code. Its raw payload is existentially
bound by an actualJ graph, not replaced by a presumed canonical application. -/
def pairedApplicationGraph {α : Type} (Gamma : List Ty) (data : Data)
    (out domain codomain function argument : OTerm α) : Formula α :=
  existsOne
    (InternalCanonicalQuotientEdgeApplicationLift.applicationGraph data (.var (.inr 0))
        (domain.relabel Sum.inl) (codomain.relabel Sum.inl)
        (function.relabel Sum.inl) (argument.relabel Sum.inl) ⊓
      graph2 InternalPairing.pairing (out.relabel Sum.inl)
        (numeral (Encodable.encode Gamma)) (.var (.inr 0)))

/-- Exact test-zero fallback, with all original coordinates and actual out
unchanged. This is a conclusion, never a field of the canonical Data. -/
def ZeroLaw {m : Nat} (test dispatched old : Program m) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (xs : Fin m → OTerm α) (out : OTerm α),
  Nonempty (Derivation body Delta
    ((programGraph test OrdinaryArithmetic.zeroTerm xs).imp
      ((programGraph dispatched out xs).iff (programGraph old out xs))))

/-- Graph-only laws of ONE selection, all before arbitrary bodies, variable
types, contexts and symbolic terms. No path/package closure is asserted. -/
def InternalLaws (window : Nat) (Gamma : List Ty) (data : Data)
    (oldPositive : Program 4) (oldTyped : Program 3) (oldResult : Program 5) : Prop :=
  (∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
      (context functionObject targetObject source target certificate out : OTerm α),
    Nonempty (Derivation body Delta
      ((positivePremises window Gamma context functionObject targetObject source target).imp
        ((programGraph (positive window Gamma data oldPositive) out
            (positiveArguments context functionObject targetObject certificate)).iff
          (graph3 (InternalPathChecker.checker
            (InternalCanonicalQuotientEdgeSelection.edgeChecker data) true)
            out source target certificate))))) ∧
  (∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
      (context typ object payload out : OTerm α),
    Nonempty (Derivation body Delta
      ((typedPremises window Gamma context object payload).imp
        ((programGraph (typed window Gamma data oldTyped) out
            (typedArguments context typ object)).iff
          (graph2 (InternalCanonicalDescentSelection.selectedTyped data) out payload typ))))) ∧
  (∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
      (context domain codomain functionObject argumentObject function argument out : OTerm α),
    Nonempty (Derivation body Delta
      ((resultPremises window Gamma data context domain codomain
          functionObject argumentObject function argument).imp
        ((programGraph (result window Gamma data oldResult) out
            (resultArguments context domain codomain functionObject argumentObject)).iff
          (pairedApplicationGraph Gamma data out domain codomain function argument))))) ∧
  ZeroLaw (positiveActivation window Gamma) (positive window Gamma data oldPositive) oldPositive ∧
  ZeroLaw (typedActivation window Gamma) (typed window Gamma data oldTyped) oldTyped ∧
  ZeroLaw (resultActivation window Gamma data) (result window Gamma data oldResult) oldResult

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatch
