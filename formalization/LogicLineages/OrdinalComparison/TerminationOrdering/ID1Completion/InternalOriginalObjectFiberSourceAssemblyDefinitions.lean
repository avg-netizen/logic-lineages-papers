module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatchDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationGuardedDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceAssembly
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Executable leaves ONLY. Selection follows the fixed finite window and
Gamma, and precedes every body, type, derivation context and symbolic term.
No calibration, closure, reflection or certified-lift proof is stored here. -/
structure Selection where
  canonical : InternalCanonicalDescentSelection.Data
  oldSource : SourcePresentation.Data
  oldComp : JointGammaComputability.Data
  oldResult : Program 5
  oldVertex : Program 5
  oldLift : Program 5
  window : Program 1

/-- Only the positive field changes. All other source leaves are literal old
leaves, including the original multiset/direct pair. -/
def patchedSource (K : Nat) (Gamma : List Ty) (p : Selection) : SourcePresentation.Data :=
  { p.oldSource with positive := (InternalOriginalObjectFiberSourceDispatch.positive
      K Gamma p.canonical p.oldSource.positive) }

/-- Only the typed field changes. The old guard and application remain the
exact old leaves at this stage. -/
def patchedComp (K : Nat) (Gamma : List Ty) (p : Selection) : JointGammaComputability.Data :=
  { p.oldComp with typed := (InternalOriginalObjectFiberSourceDispatch.typed
      K Gamma p.canonical p.oldComp.typed) }

def patchedResult (K : Nat) (Gamma : List Ty) (p : Selection) : Program 5 :=
  InternalOriginalObjectFiberSourceDispatch.result K Gamma p.canonical p.oldResult

/-- The concrete gamma, validity, tag and arrow ASTs are not reselected.
The valid-window AST may remain an externally calibrated global witness. -/
def src (K : Nat) (Gamma : List Ty) (p : Selection) : SourcePresentation.Data :=
  GammaGuardedSource.source (patchedSource K Gamma p) (patchedComp K Gamma p).typed
    InternalOriginalObjectFiberSourceDispatch.valid
    InternalOriginalObjectFiberSourceDispatch.gamma
    InternalOriginalObjectFiberSourceDispatch.tag p.window

def baseComp (K : Nat) (Gamma : List Ty) (p : Selection) : JointGammaComputability.Data :=
  GammaGuardedSource.computability (patchedComp K Gamma p)
    InternalOriginalObjectFiberSourceDispatch.valid
    InternalOriginalObjectFiberSourceDispatch.gamma
    InternalOriginalObjectFiberSourceDispatch.tag

def comp (K : Nat) (Gamma : List Ty) (p : Selection) : JointGammaComputability.Data :=
  InternalApplication.computability (baseComp K Gamma p) p.window
    InternalOriginalObjectFiberSourceDispatch.arrow (patchedResult K Gamma p)

def selectedVertex (K : Nat) (p : Selection) : Program 5 :=
  InternalCanonicalFixedWindowVertexDispatch.vertex K p.canonical p.oldVertex

/-- The exact existing original outer path dispatcher and raw-list mapper.
Neither the object code nor the path entries or oldLift fallback change. -/
def lift (K : Nat) (Gamma : List Ty) (p : Selection) : Program 5 :=
  InternalOriginalObjectFiberPathDispatch.dispatch Gamma (selectedVertex K p) p.oldLift

def WindowCalibrated (n : Nat) (window : Program 1) : Prop :=
  ∀ xs, evaluate window xs = GuardCalibration.validWindowValue n xs

/-- External all-input contracts of the selected leaves, not Data fields.
There is no internal semantic-reflection or path-preservation hypothesis. -/
def InputsCalibrated (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (p : Selection) : Prop :=
  InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table p.canonical ∧
  ContextUniform.Calibrated p.oldSource n arity ∧
  JointGammaComputability.Calibrated p.oldComp n arity ∧
  InternalOriginalObjectFiberSourceDispatch.ResultCalibrated n arity p.oldResult ∧
  InternalApplicationPathMap.VertexCalibrated n arity Gamma p.oldVertex ∧
  InternalOriginalObjectFiberPathDispatch.PathValueCalibrated n arity p.oldLift ∧
  WindowCalibrated n p.window

def PatchedCalibrated (n : Nat) (arity : Fin n → Nat)
    (K : Nat) (Gamma : List Ty) (p : Selection) : Prop :=
  ContextUniform.Calibrated (patchedSource K Gamma p) n arity ∧
  JointGammaComputability.Calibrated (patchedComp K Gamma p) n arity ∧
  InternalOriginalObjectFiberSourceDispatch.ResultCalibrated n arity (patchedResult K Gamma p)

/-- Every equality in these original interfaces quantifies over ALL natural
input vectors, including inactive windows, other Gamma fibers and defaults. -/
def AssembledCalibrated (n : Nat) (arity : Fin n → Nat)
    (K : Nat) (Gamma : List Ty) (p : Selection) : Prop :=
  ContextUniform.Calibrated (src K Gamma p) n arity ∧
  JointGammaComputability.Calibrated (baseComp K Gamma p) n arity ∧
  JointGammaComputability.Calibrated (comp K Gamma p) n arity ∧
  InternalOriginalObjectFiberSourceDispatch.ResultCalibrated n arity (patchedResult K Gamma p) ∧
  InternalApplicationPathMap.VertexCalibrated n arity Gamma (selectedVertex K p) ∧
  InternalCanonicalFixedWindowPathLift.LiftPathCalibrated n arity Gamma (selectedVertex K p) ∧
  InternalCanonicalFixedWindowPathLift.PathValueOnDecodedArgument n arity Gamma (selectedVertex K p) ∧
  InternalOriginalObjectFiberPathDispatch.PathValueCalibrated n arity (lift K Gamma p)

/-- Actual arithmetic graph laws of this SAME canonical/source/path package.
This collects earlier dispatch/path facts; it is NOT a certified source lift. -/
def GraphLaws (K : Nat) (Gamma : List Ty) (p : Selection) : Prop :=
  InternalCanonicalQuotientEdgeSelection.InternalLaws p.canonical ∧
  InternalCanonicalQuotientEdgeApplicationLift.InternalLaws p.canonical ∧
  InternalOriginalObjectFiberSourceDispatch.InternalLaws K Gamma p.canonical
    p.oldSource.positive p.oldComp.typed p.oldResult ∧
  InternalCanonicalFixedWindowVertexDispatch.InternalLaws K p.canonical p.oldVertex ∧
  InternalCanonicalFixedWindowVertexDispatch.InvariantLaws K p.canonical ∧
  InternalCanonicalFixedWindowPathLift.InternalLaws K p.canonical p.oldVertex ∧
  InternalOriginalObjectFiberPathDispatch.InternalLaws Gamma (selectedVertex K p) p.oldLift

/-- Generic construction-level typed closure at this exact src/comp.
The body and Delta are arbitrary, not semantic source-model premises. -/
def TypedClosure (K : Nat) (Gamma : List Ty) (p : Selection) (context : Nat) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α)) (typ x y : OTerm α),
  Nonempty (Derivation body Delta
    ((GuardedSource.literalTyped (comp K Gamma p) context typ x ⊓
      GuardedSource.literalR (src K Gamma p) context x y).imp
      (GuardedSource.literalTyped (comp K Gamma p) context typ y)))

/-- Ground accessibility uses the literal SAME selected source body. -/
def GroundClosure (K : Nat) (Gamma : List Ty) (p : Selection) (context : Nat) : Prop :=
  ∀ (α : Type) (Delta : List (Formula α)) (x y : OTerm α),
  Nonempty (Derivation (SourcePresentation.sourceBody (src K Gamma p) context) Delta
    ((GuardedSource.literalComputable (comp K Gamma p) context .ground x ⊓
      GuardedSource.literalR (src K Gamma p) context x y).imp
      (GuardedSource.literalComputable (comp K Gamma p) context .ground y)))

/-- No selected-context equality or window-validity premise is required. -/
def GuardTransport (K : Nat) (Gamma : List Ty) (p : Selection) (context : Nat) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α)) (typ x y u : OTerm α),
  Nonempty (Derivation body Delta
    (((GuardedSource.literalTyped (comp K Gamma p) context typ x ⊓
      GuardedSource.literalR (src K Gamma p) context x y) ⊓
      GammaGuardedSource.literalGuard (comp K Gamma p) y u).imp
      (GammaGuardedSource.literalGuard (comp K Gamma p) x u)))

def ApplicationTotality (K : Nat) (Gamma : List Ty) (p : Selection) (context : Nat) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (sigma tau : Ty) (f a : OTerm α),
  Nonempty (Derivation body Delta
    ((ApplicationGuarded.domain (comp K Gamma p) context sigma tau f a).imp
      (ApplicationGuarded.existsApplication (comp K Gamma p) context sigma tau f a)))

def ApplicationFunctionality (K : Nat) (Gamma : List Ty) (p : Selection) (context : Nat) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (sigma tau : Ty) (f a out other : OTerm α),
  Nonempty (Derivation body Delta
    ((ApplicationGuarded.domain (comp K Gamma p) context sigma tau f a).imp
      ((InternalApplication.literalApplication (comp K Gamma p).application context sigma tau f a out ⊓
        InternalApplication.literalApplication (comp K Gamma p).application context sigma tau f a other).imp
        (InternalControlGraph.equal out other))))

def ApplicationComputability (K : Nat) (Gamma : List Ty) (p : Selection) (context : Nat) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (sigma tau : Ty) (f a out : OTerm α),
  Nonempty (Derivation body Delta
    ((InternalComputabilityApplication.premises (comp K Gamma p) sigma tau (numeral context) f a).imp
      ((InternalComputabilityApplication.accepted (comp K Gamma p) sigma tau (numeral context) f a out).imp
        (InternalComputabilityApplication.computable (comp K Gamma p) tau (numeral context) out))))

def ResultComputability (K : Nat) (Gamma : List Ty) (p : Selection) (context : Nat) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (sigma tau : Ty) (f a out : OTerm α),
  Nonempty (Derivation body Delta
    ((InternalComputabilityApplication.premises (comp K Gamma p) sigma tau (numeral context) f a).imp
      ((InternalControlGraph.programGraph (patchedResult K Gamma p) out
        (InternalComputabilityApplication.arguments (numeral context) sigma tau f a)).imp
        (InternalComputabilityApplication.computable (comp K Gamma p) tau (numeral context) out))))

/-- The selected package does not change when the source context varies.
Window acceptance is discharged for every ORIGINAL closed finite window;
no new package is selected under the quantified source symbols or types. -/
def SourceLaws (n : Nat) (K : Nat) (Gamma : List Ty) (p : Selection) : Prop :=
  (∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
    SubtypeClosed (fun typ => typ ∈ S) →
    let context := OrdinaryArithmeticQuotient.contextCode symbols S table
    TypedClosure K Gamma p context ∧
    GroundClosure K Gamma p context ∧
    ApplicationTotality K Gamma p context ∧
    ApplicationFunctionality K Gamma p context ∧
    ApplicationComputability K Gamma p context ∧
    ResultComputability K Gamma p context) ∧
  (∀ context : Nat, GuardTransport K Gamma p context)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceAssembly
