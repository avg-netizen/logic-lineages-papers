module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceAssemblyDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceAssemblyTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalOriginalObjectFiberSourceAssembly
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Exact Program equalities expose the unchanged old leaves and fallback.
The normalized guard is concrete valid/gamma; it is not the old guard AST. -/
def ActualOriginalObjectAssemblyPreservedLeaves : Prop :=
  ∀ (K : Nat) (Gamma : List Ty) (p : Selection),
    (patchedSource K Gamma p).scalar = p.oldSource.scalar ∧
    (patchedSource K Gamma p).multiset = p.oldSource.multiset ∧
    (patchedSource K Gamma p).direct = p.oldSource.direct ∧
    (patchedComp K Gamma p).guard = p.oldComp.guard ∧
    (patchedComp K Gamma p).application = p.oldComp.application ∧
    (src K Gamma p).scalar = p.oldSource.scalar ∧
    (src K Gamma p).multiset = p.oldSource.multiset ∧
    (src K Gamma p).direct = p.oldSource.direct ∧
    (baseComp K Gamma p).application = p.oldComp.application ∧
    (comp K Gamma p).typed = (baseComp K Gamma p).typed ∧
    (comp K Gamma p).guard = (baseComp K Gamma p).guard ∧
    (comp K Gamma p).guard = GammaGuardedSource.guard
      InternalOriginalObjectFiberSourceDispatch.valid InternalOriginalObjectFiberSourceDispatch.gamma ∧
    (comp K Gamma p).application = InternalApplication.application
      (ApplicationDomain.activation p.window (baseComp K Gamma p).typed
        (baseComp K Gamma p).guard InternalOriginalObjectFiberSourceDispatch.arrow)
      (patchedResult K Gamma p) p.oldComp.application

/-- Universal over an already selected package. No existential source
witness may be exchanged for its separately selected path data. -/
def ActualOriginalObjectAssemblyPatchedCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (p : Selection),
  SubtypeClosed (fun typ => typ ∈ S) →
  InputsCalibrated n arity symbols S Gamma table p →
  PatchedCalibrated n arity (OrdinaryArithmeticQuotient.contextCode symbols S table) Gamma p

/-- Original ALL-input src, baseComp, comp, result, vertex, raw mapper and
outer pathValue calibration, all for the literal SAME selected Programs. -/
def ActualOriginalObjectAssemblyCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (p : Selection),
  SubtypeClosed (fun typ => typ ∈ S) →
  InputsCalibrated n arity symbols S Gamma table p →
  AssembledCalibrated n arity (OrdinaryArithmeticQuotient.contextCode symbols S table) Gamma p

/-- Construction-level closure at arbitrary leaves, body, Delta and terms.
Only an actual CLOSED window numeral evaluation is discharged externally. -/
def ActualInternalOriginalObjectAssemblyTypedClosure : Prop :=
  ∀ (K : Nat) (Gamma : List Ty) (p : Selection) (context : Nat),
  evaluate p.window (List.Vector.ofFn ![context]) = 1 →
  TypedClosure K Gamma p context

/-- Scalar inversion is instantiated at src itself and combined with the
SAME comp's typed closure. No unrelated existential ground-closure supplier. -/
def ActualInternalOriginalObjectAssemblyGroundClosure : Prop :=
  ∀ (K : Nat) (Gamma : List Ty) (p : Selection) (context : Nat),
  evaluate p.window (List.Vector.ofFn ![context]) = 1 →
  GroundClosure K Gamma p context

/-- The actual generic gamma-guard transport is specialized to the patched
leaves. It is unconditional on the context, window and canonical calibration. -/
def ActualInternalOriginalObjectAssemblyGuardTransport : Prop :=
  ∀ (K : Nat) (Gamma : List Ty) (p : Selection) (context : Nat),
  GuardTransport K Gamma p context

/-- The domain remains the original typed-function, typed-argument and
same-Gamma formulas. The closed arrow metadata uses the concrete cons AST. -/
def ActualInternalOriginalObjectAssemblyApplicationTotality : Prop :=
  ∀ (K : Nat) (Gamma : List Ty) (p : Selection) (context : Nat),
  evaluate p.window (List.Vector.ofFn ![context]) = 1 →
  ApplicationTotality K Gamma p context

/-- Both actual supplied outputs belong to the SAME assembled application
checker. Equality is internally derived, not externally reflected. -/
def ActualInternalOriginalObjectAssemblyApplicationFunctionality : Prop :=
  ∀ (K : Nat) (Gamma : List Ty) (p : Selection) (context : Nat),
  evaluate p.window (List.Vector.ofFn ![context]) = 1 →
  ApplicationFunctionality K Gamma p context

/-- Original higher-type computability with its negative occurrences and
same-Gamma premise intact; activation is derived rather than assumed. -/
def ActualInternalOriginalObjectAssemblyApplicationComputability : Prop :=
  ∀ (K : Nat) (Gamma : List Ty) (p : Selection) (context : Nat),
  evaluate p.window (List.Vector.ofFn ![context]) = 1 →
  ApplicationComputability K Gamma p context

/-- Computability at the raw output of the SAME patched original builder.
The builder and application checker are not chosen independently afterward. -/
def ActualInternalOriginalObjectAssemblyResultComputability : Prop :=
  ∀ (K : Nat) (Gamma : List Ty) (p : Selection) (context : Nat),
  evaluate p.window (List.Vector.ofFn ![context]) = 1 →
  ResultComputability K Gamma p context

/-- ONE selection is made AFTER the selected original window and Gamma and
BEFORE all bodies, types, source contexts, Delta and symbolic terms. The
source and path packages share canonical E/T/J, old programs and window AST.
This is source-package assembly only, not fiberCertifiedLift or its transport
bridge; no uniform varying-Gamma selection or all-type downward claim. -/
def ActualOriginalSelectedObjectFiberSourceAssembly : Prop :=
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
    SourceLaws n K Gamma p

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceAssemblyTargets
