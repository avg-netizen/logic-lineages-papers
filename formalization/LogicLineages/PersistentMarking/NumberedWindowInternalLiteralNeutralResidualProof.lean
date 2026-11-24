module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDirectCarrierInstalledProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFreshNeutralBridgeProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralResidualProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.OrdinalComparison.Source (Ty)
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (carrier membership)
open ID1Completion.SourcePresentation (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenH)
open NumberedWindowInternalNeutralFactsTargets (Arithmetic D atom direct inherited)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalLiteralDirectCarrierInstalledProof
  (Raw DirectRules Packet exact_ConcreteLiteralDirectCarrierTuple)
open NumberedWindowInternalAtomicRefinement (freeSource)
open NumberedWindowComputabilityFormulaTargets (accepts formula)
open NumberedWindowInternalProbeTargets (typedAt)
open NumberedWindowInternalPullbackTargets (ForwardRule)
open NumberedWindowInternalLiteralFreshNeutralBridgeProof (exact_TupleComputabilityToIFromArithmetic)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)

/-- The residual neutral arithmetic after discharging first-hop and
target-carrier on the very same ordinary original body. No new
assumption about probes or open typing is necessary. -/
structure Residual (s : Data) (p h : Program 3) (n b : Program 1) (c : Nat) : Prop where
  bottomNeutral : ∀ (α : Type) (Γ : List (Formula α)) (x : OTerm α),
    D s c Γ (atom b x) → D s c Γ (atom n x)
  bottomNoStep : ∀ (α : Type) (Γ : List (Formula α)) (x y : OTerm α),
    D s c Γ (atom b x) → D s c Γ (direct s h c x y) → D s c Γ ⊥
  variableNeutral : ∀ (α : Type) (Γ : List (Formula α)) (x : OTerm α),
    D s c Γ (atom freeSource x) → D s c Γ (atom n x)
  variableStep : ∀ (α : Type) (Γ : List (Formula α)) (x y : OTerm α),
    D s c Γ (atom freeSource x) → D s c Γ (direct s h c x y) → D s c Γ (atom b y)
  applicationNeutral : ∀ (α : Type) (Γ : List (Formula α)) (x u t : OTerm α),
    D s c Γ (atom n x) → D s c Γ (accepts p x u t) →
    D s c Γ (carrier s false c t) ∧ D s c Γ (atom n t)
  applicationInversion : ∀ (α : Type) (Γ : List (Formula α)) (x u t y : OTerm α),
    D s c Γ (atom n x) → D s c Γ (accepts p x u t) →
    D s c Γ (direct s h c t y) → D s c Γ (atom b y ⊔ inherited s p h c x u y)

abbrev Body (i cv tv : Program 1) (raw : Program 5) (L : Program 3) :=
  S i cv tv (Raw i cv tv raw L) L

abbrev Step (i cv tv : Program 1) (raw : Program 5) (L : Program 3) :=
  hop cv tv (Raw i cv tv raw L) L

theorem exact_LiteralArithmeticFromResidual (i cv tv : Program 1) (raw : Program 5)
    (L p : Program 3) (n b : Program 1) (c : Nat) (checked : DirectRules i cv tv raw L)
    (left : Residual (Body i cv tv raw L) p (Step i cv tv raw L) n b c) :
    Arithmetic (Body i cv tv raw L) p (Step i cv tv raw L) n b freeSource c :=
  ⟨checked.first c,checked.targetCarrier c,left.bottomNeutral,left.bottomNoStep,left.variableNeutral,
    left.variableStep,left.applicationNeutral,left.applicationInversion⟩

/-- All components here live on one physically selected body. The two
verified direct rules and installed literal fresh probes reduce typed
computability-to-membership to the stated six residual neutral rules
and genuine positive application forward transport. -/
theorem exact_LiteralTypedMembershipFromResidual (xs : Entries) (s : Settings) (W : List ProbeTy)
    (i cv tv : Program 1) (raw : Program 5) (L p₀ : Program 3) (v : Inputs)
    (packet : Packet xs s W i cv tv raw L p₀ v) (c : Nat) (n b : Program 1)
    (left : Residual (Body i cv tv raw L) v.applicationGuard (Step i cv tv raw L) n b c)
    (forward : ForwardRule (Body i cv tv raw L) v.applicationGuard c)
    (τ : Ty) (α : Type) (Γ : List (Formula α)) (q : OTerm α) :
    D (Body i cv tv raw L) c Γ (typedAt (chosenH v W) τ q) →
    D (Body i cv tv raw L) c Γ (formula v.applicationGuard τ q) →
    D (Body i cv tv raw L) c Γ (membership false q) := by
  let R := Raw i cv tv raw L
  let r := addressPositive cv tv R L
  let d := dCore i r permutation
  exact exact_TupleComputabilityToIFromArithmetic xs s W i (jRaw i) r d v c
    (Step i cv tv raw L) n b packet.physical.1
    (exact_LiteralArithmeticFromResidual i cv tv raw L v.applicationGuard n b c packet.directRules left)
    forward τ α Γ q

#print axioms exact_LiteralArithmeticFromResidual
#print axioms exact_LiteralTypedMembershipFromResidual
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralResidualProof
