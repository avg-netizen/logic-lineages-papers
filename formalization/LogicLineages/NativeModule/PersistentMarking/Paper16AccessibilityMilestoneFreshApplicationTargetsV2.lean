module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneArrowTypingInstallTargetsV2
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendDefinitions

/-! Frozen targets: the two least-program facts behind `FreshApplicationTotal`
(`lem:arithmetic-accessibility`, type split at arrow types; Fable B, 27 November 2026).

`FreshAddressCarrier` (K1): the fresh address selected for an admitted arrow address is itself a
scalar carrier. `FreshSeedLeast` (K2): the installed least program returns a successor on the
application seed built from that arrow address and its fresh address. Both are stated for the
fresh probe only, which is the case the numerical window validity covers.

`FreshApplicationFromLeast` is the finite-shape reduction of `FreshApplicationTotal` to K1 and K2
on any window whose application guard is the installed guarded core.
`InstalledAccessibilityFromLeast` composes it with the reduction on the joined lambda window with
literal probe leaves. Neither K1 nor K2 is asserted here. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFreshApplicationTargetsV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules ID1Completion.SourcePresentation
open ID1Completion.InternalControlGraph
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets (sourceWindow)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeParsedTyped (chosenA)
open NumberedWindowInternalProbeTargets (OTerm freshAt)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open Paper16AccessibilityMilestoneTargetsV2
  (InstalledWindow CarrierTypingCases TypedCarrierComputability AllTerms)
open Paper16AccessibilityMilestoneArrowTypingTargetsV2 (storedType FreshApplicationTotal)

variable {S : Spine.Signature} {K : List Ty} {W : List ProbeTy}

/-- The least program returns some successor at the given context, type and seed. Only the
selected representative is bound. -/
def leastSelectedAt {α : Type} (L : Program 3) (ctx ty seed : OTerm α) : Formula α :=
  let j : α → α ⊕ Fin 1 := Sum.inl
  let k : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  existsOne (programGraph L (suc k) ![ctx.relabel j, ty.relabel j, seed.relabel j])

/-- K1. The fresh address selected for an admitted address of a listed arrow type is a scalar
carrier. -/
def FreshAddressCarrier (A : InstalledWindow S K W) (c : Nat) : Prop :=
  ∀ (σ τ : ProbeTy), (.arrow σ τ : ProbeTy) ∈ W →
    ∀ (α : Type) (Γ : List (Formula α)) (q u : OTerm α),
      Nonempty (Derivation (sourceBody A.presentation c) Γ (carrier A.presentation false c q)) →
      Nonempty (Derivation (sourceBody A.presentation c) Γ (storedType (.arrow σ τ) q)) →
      Nonempty (Derivation (sourceBody A.presentation c) Γ (freshAt (chosenA A.probes) q u)) →
      Nonempty (Derivation (sourceBody A.presentation c) Γ (carrier A.presentation false c u))

/-- K2. For an admitted address `q` of a listed arrow type and its selected fresh address `u`,
both carriers, with reported fields `ctx`, `rawCons dom cod`, `fn` and `ctx`, `dom`, `arg`, the
installed least program returns a successor on the application seed
`auxiliaryTerm dom cod fn arg` at context `ctx` and type `cod`. -/
def FreshSeedLeast (A : InstalledWindow S K W) (c : Nat) : Prop :=
  ∀ (σ τ : ProbeTy), (.arrow σ τ : ProbeTy) ∈ W →
    ∀ (α : Type) (Γ : List (Formula α)) (q u ctx dom cod fn arg : OTerm α),
      Nonempty (Derivation (sourceBody A.presentation c) Γ (carrier A.presentation false c q)) →
      Nonempty (Derivation (sourceBody A.presentation c) Γ (carrier A.presentation false c u)) →
      Nonempty (Derivation (sourceBody A.presentation c) Γ (storedType (.arrow σ τ) q)) →
      Nonempty (Derivation (sourceBody A.presentation c) Γ (freshAt (chosenA A.probes) q u)) →
      Nonempty (Derivation (sourceBody A.presentation c) Γ
        (addressReport q ctx (rawCons dom cod) fn)) →
      Nonempty (Derivation (sourceBody A.presentation c) Γ (addressReport u ctx dom arg)) →
      Nonempty (Derivation (sourceBody A.presentation c) Γ
        (leastSelectedAt A.least ctx cod (auxiliaryTerm dom cod fn arg)))

/-- The fresh application from K1 and K2, on any window whose application guard is the
installed guarded core. -/
def FreshApplicationFromLeast : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty) (W : List ProbeTy) (A : InstalledWindow S K W),
    A.probes.applicationGuard = applicationGuard A.scalar A.least →
    ∀ c : Nat, FreshAddressCarrier A c → FreshSeedLeast A c → FreshApplicationTotal A c

/-- For every closed source universe there is one installed window on which the type split
follows from K1 and K2, and the all-terms sentence from the type split and typed carrier
computability. -/
def InstalledAccessibilityFromLeast : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    ∃ A : InstalledWindow S K (sourceWindow K), ∀ c : Nat,
      (FreshAddressCarrier A c → FreshSeedLeast A c → CarrierTypingCases A c) ∧
      (CarrierTypingCases A c → TypedCarrierComputability A c → AllTerms A c)

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFreshApplicationTargetsV2
