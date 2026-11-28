module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalUpperUniformTargets
public import LogicLineages.NativeModule.PersistentMarking.ConditionalJSingletonTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowOriginalComputabilityFormulaTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHopCarrierDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionLiteralJTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalProbeTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneTargetsV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules ID1Completion.SourcePresentation
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowOriginalComputabilityFormulaTargets (formulaType)
open NumberedWindowFormulaCalibrationTargets NumberedWindowPresentationCheckers
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenA chosenH)
open NumberedWindowInternalSparseTuple (InstalledTupleAt)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData LiteralJUnion)
open NumberedWindowInternalCertifiedUnionStepProof (CertifiedOriginSplit unionGraph)

/-- One choice of the installed original programs for a fixed finite source
window. All subsequent obligations refer to this physical selection. -/
structure InstalledWindow (S : Spine.Signature) (K : List Ty) (W : List ProbeTy) where
  valid : ValidWindow (fixed S K) W
  scalar : Program 1
  contextGuard : Program 1
  typeGuard : Program 1
  raw : Program 5
  least : Program 3
  application : Program 3
  probes : Inputs
  installed :
    let R := rawWithTarget scalar contextGuard typeGuard raw least
    let r := addressPositive contextGuard typeGuard R least
    InstalledTupleAt S.entries (fixed S K) W scalar (jRaw scalar) contextGuard typeGuard
      (dCore scalar r permutation) application R least probes

variable {S : Spine.Signature} {K : List Ty} {W : List ProbeTy}

def InstalledWindow.path (A : InstalledWindow S K W) : Program 3 :=
  addressPositive A.contextGuard A.typeGuard
    (rawWithTarget A.scalar A.contextGuard A.typeGuard A.raw A.least) A.least

def InstalledWindow.presentation (A : InstalledWindow S K W) : Data :=
  literalData A.scalar A.path

/-- The numeric meaning of the four installed programs, projected from
`InstalledTupleAt` through its `TupleAt` component. -/
def InstalledWindow.Calibrated (A : InstalledWindow S K W) : Prop :=
  Evaluates (checks S.entries (fixed S K)) A.scalar (jRaw A.scalar) A.path
    (dCore A.scalar A.path permutation)

theorem InstalledWindow.calibrated (A : InstalledWindow S K W) : A.Calibrated :=
  A.installed.1.1

/-- The two directions of application transport and the two fresh-probe
obligations for computability to imply accessibility on this window. -/
structure ApplicationArithmetic (A : InstalledWindow S K W) (c : Nat) : Prop where
  matchEdge : NumberedWindowInternalDownwardTargets.ApplicationEdgeMatching
    A.presentation A.probes.applicationGuard c
  forwardEdge : NumberedWindowInternalPullbackTargets.ForwardRule
    A.presentation A.probes.applicationGuard c
  typedProbe : NumberedWindowInternalProbeTargets.TypedProbeTotal
    A.presentation A.probes.applicationGuard (chosenH A.probes W) (chosenA A.probes) c
  freshComputable : NumberedWindowInternalProbeTargets.FreshVariablesComputable
    A.presentation A.probes.applicationGuard (chosenH A.probes W) (chosenA A.probes) c

/-- The certified split and the J-union step use exactly the installed
permutation observer and checker. -/
structure CertifiedMultisetUnion (A : InstalledWindow S K W) (c : Nat) : Prop where
  split : CertifiedOriginSplit A.presentation c permutation
  union : LiteralJUnion A.scalar A.path c

/-- The union used by the singleton and member inductions feeds the
permutation-aware union report on the same code. -/
def UnionFeedsCountedReport (A : InstalledWindow S K W) (c : Nat) (u : Program 2) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (a b out : OrdinaryArithmetic.Term α),
    Nonempty (Derivation (sourceBody A.presentation c) Γ (carrier A.presentation true c a)) →
    Nonempty (Derivation (sourceBody A.presentation c) Γ (carrier A.presentation true c b)) →
    Nonempty (Derivation (sourceBody A.presentation c) Γ (ConditionalJUnionTargets.union u a b out)) →
    Nonempty (Derivation (sourceBody A.presentation c) Γ (unionGraph permutation a b out))

/-- The remaining multiset obligations at the selected union, member and
singleton programs. The conclusion uses the certified union closure. -/
structure MultisetGeneration (A : InstalledWindow S K W) (c : Nat)
    (u mem : Program 2) (sg : Program 1) : Prop where
  unionCarrier : ConditionalJUnionTargets.CarrierUnion A.presentation c u
  unionReport : UnionFeedsCountedReport A c u
  singletonCarrier : ConditionalJSingletonTargets.SingletonCarrier A.presentation c sg
  nilCarrier : ConditionalJSingletonTargets.NilCarrier A.presentation c
  nilNoStep : ConditionalJSingletonTargets.NilNoStep A.presentation c
  descendants : ConditionalJSingletonTargets.DescendantGeneration A.presentation c u sg
  members : ConditionalJSingletonTargets.MemberGeneration A.presentation c u mem sg

def FinishMultisets (A : InstalledWindow S K W) (c : Nat) (u mem : Program 2) (sg : Program 1) : Prop :=
  CertifiedMultisetUnion A c → MultisetGeneration A c u mem sg →
    ConditionalJSingletonTargets.SingletonAccessibility A.presentation c sg ∧
    ConditionalJSingletonTargets.MembersAccessibility A.presentation c mem

/-- The constructor and structural inductions must deliver computability
for guarded scalar addresses and their type in this particular window.
The original `formulaType` converts each source type to the type of its
object-language typing and computability formulas. -/
def TypedCarrierComputability (A : InstalledWindow S K W) (c : Nat) : Prop :=
  ∀ (τ : Ty) (_ : τ ∈ K) (α : Type) (Γ : List (Formula α)) (q : OrdinaryArithmetic.Term α),
    Nonempty (Derivation (sourceBody A.presentation c) Γ (carrier A.presentation false c q)) →
    Nonempty (Derivation (sourceBody A.presentation c) Γ
      (NumberedWindowInternalProbeTargets.typedAt (chosenH A.probes W) (formulaType τ) q)) →
    Nonempty (Derivation (sourceBody A.presentation c) Γ
      (NumberedWindowComputabilityFormulaTargets.formula A.probes.applicationGuard (formulaType τ) q))

/-- The actual ID₁ sentence for all admitted auxiliary terms. -/
def AllTerms (A : InstalledWindow S K W) (c : Nat) : Prop :=
  ExternalOrdinalInterfaceID1Targets.InternalAccessibility A.presentation c

/-- The internal finite type split for a scalar address, at an arbitrary
open goal. The candidate types are the actual elements of the window. -/
def CarrierTypingCases (A : InstalledWindow S K W) (c : Nat) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (q : OrdinaryArithmetic.Term α) (goal : Formula α),
    Nonempty (Derivation (sourceBody A.presentation c) Γ (carrier A.presentation false c q)) →
    (∀ τ ∈ K, Nonempty (Derivation (sourceBody A.presentation c)
      (NumberedWindowInternalProbeTargets.typedAt (chosenH A.probes W) (formulaType τ) q :: Γ) goal)) →
    Nonempty (Derivation (sourceBody A.presentation c) Γ goal)

/-- Assemble the uniform sentence using the same presentation and
context for type coverage, computability, and the probe rules. -/
def CloseAllTerms (A : InstalledWindow S K W) (c : Nat) : Prop :=
  CarrierTypingCases A c → ApplicationArithmetic A c → TypedCarrierComputability A c →
    AllTerms A c

/-- Each closed window admits an installation of the named programs. -/
def SelectInstalledWindows : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    ∃ W : List ProbeTy, Nonempty (InstalledWindow S K W)

/-- Uniform selection and derivability for the closed source windows.
The numbered upper-bound assembly consumes the existing
ConditionalUpperUniformTargets.UniformAccessibility contract. -/
def InstalledArithmeticAccessibility : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    ∃ (W : List ProbeTy) (A : InstalledWindow S K W) (c : Nat), AllTerms A c

/-- Project the four calibrated programs and the all-terms derivation
from the installed package into the existing numbered interface. -/
def InstalledToUniform : Prop :=
  InstalledArithmeticAccessibility → ConditionalUpperUniformTargets.UniformAccessibility

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneTargetsV2
