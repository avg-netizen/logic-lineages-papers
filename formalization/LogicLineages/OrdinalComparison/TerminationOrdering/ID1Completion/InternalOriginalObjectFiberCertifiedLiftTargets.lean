module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalOriginalObjectFiberSourceAssembly InternalOriginalObjectFiberCertifiedLift
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Recover the function's fixed Gamma from the original same-Gamma guard
and the SOLE extra argument-fiber graph. No decoded object is supplied. -/
def ActualInternalOriginalObjectFunctionFiber : Prop :=
  ∀ (K : Nat) (Gamma : List Ty) (p : Selection)
    (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α)) (f a : OTerm α),
  Nonempty (Derivation body Delta
    ((InternalComputabilityApplication.guarded (comp K Gamma p) f a ⊓
      argumentFiber Gamma a).imp (argumentFiber Gamma f)))

/-- Full guarded-positive acceptance always recovers basePositive, hence the
target's Gamma. Window activation and target typing are NOT extra premises. -/
def ActualInternalOriginalObjectTargetFiber : Prop :=
  ∀ (K : Nat) (Gamma : List Ty) (p : Selection)
    (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α)) (f g witness : OTerm α),
  Nonempty (Derivation body Delta
    ((InternalAccessibilityRules.certificate (src K Gamma p) false K f g witness ⊓
      argumentFiber Gamma f).imp (argumentFiber Gamma g)))

/-- Exact assembled typed graph iff at the selected window and object fiber.
The concrete constant-one validity and left-of-right tag are discharged from
the SAME canonical typed factors; no old-typed or semantic typing rule. -/
def ActualInternalOriginalObjectFiberTypedGraph : Prop :=
  ∀ (K : Nat) (Gamma : List Ty) (p : Selection)
    (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (tau : Ty) (object payload : OTerm α),
  Nonempty (Derivation body Delta
    ((InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma object payload).imp
      ((InternalComputabilityApplication.typed (comp K Gamma p) tau (numeral K) object).iff
        (rawTyped p tau payload))))

/-- Strip only the actual guarded/basePositive wrappers, then use the SAME
patched whole-path checker. The supplied original certificate is unchanged. -/
def ActualInternalOriginalObjectFiberPositiveRecovery : Prop :=
  ∀ (K : Nat) (Gamma : List Ty) (p : Selection)
    (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (f g x y witness : OTerm α),
  Nonempty (Derivation body Delta
    (((InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma f x ⊓
      InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma g y) ⊓
      InternalAccessibilityRules.certificate (src K Gamma p) false K f g witness).imp
      (rawPositive p x y witness)))

/-- Rebuild the ENTIRE source certificate, not just its raw positive path:
patched positive, basePositive's same-Gamma, target typed and same tag. The
closed window evaluation is the only external construction metadata. -/
def ActualInternalOriginalObjectFiberPositiveReconstruction : Prop :=
  ∀ (K : Nat) (Gamma : List Ty) (p : Selection),
  evaluate p.window (List.Vector.ofFn ![K]) = 1 →
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (tau : Ty) (out other lifted rawOut rawOther : OTerm α),
  Nonempty (Derivation body Delta
    ((transportedOutputs Gamma p tau out other lifted rawOut rawOther).imp
      (InternalAccessibilityRules.certificate (src K Gamma p) false K out other lifted)))

/-- Derive every raw input witness, both function typings and the raw path
from the existing domain/certificate plus ONLY the argument fiber. Target
object typing comes from the existing actual certificateClosure derivation. -/
def ActualInternalOriginalObjectFiberInputExtraction : Prop :=
  ∀ (K : Nat) (Gamma : List Ty) (p : Selection),
  evaluate p.window (List.Vector.ofFn ![K]) = 1 →
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (sigma tau : Ty) (f g a witness : OTerm α),
  Nonempty (Derivation body Delta
    (((InternalComputabilityDownward.domain (comp K Gamma p) K sigma tau f a ⊓
      InternalAccessibilityRules.certificate (src K Gamma p) false K f g witness) ⊓
      argumentFiber Gamma a).imp
      (inputDataExists Gamma p sigma tau f g a witness)))

/-- Intermediate graph recovery at actual raw coordinates. Original domain
activation and the typed result-dispatch activation are DERIVED. activeRecover
exposes the SAME patchedResult, whose graph yields an existential actualJ
payload AND the original pair graph of the supplied output object. -/
def ActualInternalOriginalObjectFiberApplicationResult : Prop :=
  ∀ (K : Nat) (Gamma : List Ty) (p : Selection),
  evaluate p.window (List.Vector.ofFn ![K]) = 1 →
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (sigma tau : Ty) (f a x u out : OTerm α),
  Nonempty (Derivation body Delta
    (((InternalComputabilityDownward.domain (comp K Gamma p) K sigma tau f a ⊓
      (InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma f x ⊓
        InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma a u)) ⊓
      InternalComputabilityApplication.accepted (comp K Gamma p) sigma tau (numeral K) f a out).imp
      (InternalOriginalObjectFiberSourceDispatch.pairedApplicationGraph Gamma p.canonical
        out (numeral (typeNumber sigma)) (numeral (typeNumber tau)) x u)))

/-- All input and output raw witnesses are internally eliminated. Both
original accepted applications yield actualJ/pair outputs, raw activation
aligns them with the SAME selected vertex, and the actual outer lift graph
aligns with the unchanged mapper. Fixed-window positive path transport and
raw output typing are conclusions, not premises. -/
def ActualInternalOriginalObjectFiberRawTransport : Prop :=
  ∀ (S : List Ty) (K : Nat) (Gamma : List Ty) (p : Selection),
  InternalStructuralEndpointGuard.MembershipCalibrated S p.canonical.member →
  SubtypeClosed (fun typ => typ ∈ S) →
  evaluate p.window (List.Vector.ofFn ![K]) = 1 →
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (sigma tau : Ty) (f g a out other witness lifted : OTerm α),
  Nonempty (Derivation body Delta
    ((fiberPremises (src K Gamma p) (comp K Gamma p) (lift K Gamma p)
      K Gamma sigma tau f g a out other witness lifted).imp
      (transportedOutputsExist Gamma p tau out other lifted)))

/-- Full same-package arithmetic source-to-source acceptance, with the exact
minimal fiber-qualified antecedent and no raw/output witness premises. -/
def ActualInternalOriginalObjectFiberSourceLift : Prop :=
  ∀ (S : List Ty) (K : Nat) (Gamma : List Ty) (p : Selection),
  InternalStructuralEndpointGuard.MembershipCalibrated S p.canonical.member →
  SubtypeClosed (fun typ => typ ∈ S) →
  evaluate p.window (List.Vector.ofFn ![K]) = 1 →
  LiftAtAnyBody K Gamma p

/-- Exact original sourceBody/empty-context consumer, qualified by just the
actual argument fiber. This is NOT unqualified CertifiedApplicationLift and
does not discharge its use in the existing all-type downward reduction. -/
def ActualInternalOriginalObjectFiberCertifiedApplicationLift : Prop :=
  ∀ (S : List Ty) (K : Nat) (Gamma : List Ty) (p : Selection),
  InternalStructuralEndpointGuard.MembershipCalibrated S p.canonical.member →
  SubtypeClosed (fun typ => typ ∈ S) →
  evaluate p.window (List.Vector.ofFn ![K]) = 1 →
  FiberCertifiedApplicationLift (src K Gamma p) (comp K Gamma p) (lift K Gamma p) K Gamma

/-- Extend the exact existing assembly selection, after the fixed original
window/Gamma and before every body/type/Delta/term. Retain every original
all-input calibration and internal assembly law for the SAME p. Internal lift
acceptance still requires argumentFiber; calibration cannot remove it. -/
def ActualOriginalSelectedObjectFiberCertifiedApplicationLift : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun typ => typ ∈ S) →
  ∃ p : Selection,
    let K := OrdinaryArithmeticQuotient.contextCode symbols S table
    InputsCalibrated n arity symbols S Gamma table p ∧
    InternalCanonicalQuotientEdgeSelection.SelectedCalibrated n arity symbols S Gamma table p.canonical ∧
    InternalCanonicalQuotientEdgeApplicationLift.ApplicationCalibrated n arity symbols S Gamma p.canonical ∧
    PatchedCalibrated n arity K Gamma p ∧
    AssembledCalibrated n arity K Gamma p ∧
    GraphLaws K Gamma p ∧
    SourceLaws n K Gamma p ∧
    LiftAtAnyBody K Gamma p ∧
    FiberCertifiedApplicationLift (src K Gamma p) (comp K Gamma p) (lift K Gamma p) K Gamma

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLiftTargets
