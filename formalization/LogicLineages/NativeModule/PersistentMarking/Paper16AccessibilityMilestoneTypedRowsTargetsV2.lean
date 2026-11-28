module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneTargetsV2
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralConcreteBetaJoinedRulesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsTargets
public import LogicLineages.PersistentMarking.NumberedWindowComputabilityFormulaTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralAtomProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedBetaOutcomeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAddressedChildReportsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendDefinitions

/-! Frozen targets: the rows of `TypedCarrierComputability` on an installed window that carries
the joined beta rules (`lem:arithmetic-accessibility`, the computability facts, the lambda fact
and the closing split; map in
`verification/local-fable-trio-2026-11-27/fableB3/TYPED-COMPUTABILITY-MAP.md`; Fable B3,
27 November 2026).

Every statement is about an arbitrary `A : InstalledWindow S K W` together with
`JoinedAt A L₀ U c`, the `BetaJoinedRulesAt` package at the window's own programs. The window of
`Paper16AccessibilityMilestoneFreshCarrierTargetsV2.FrontLiteralWindowTyping` exports exactly
that package and the guard equation `A.probes.applicationGuard = applicationGuard A.scalar A.least`,
so every row applies to it. All rows are written with `windowApp A := applicationGuard A.scalar
A.least`; only the closing statement mentions `A.probes.applicationGuard`.

Proved rows (statements to be proved in `…TypedRowsProofV2`):

* `WindowNeutralFacts` — the neutral lemma, bottoms and free variables at every type
  (map rows N1–N3).
* `WindowBetaApplication` — an accepted application is computable when the function's direct
  reducts are computable at the arrow type, the argument is computable, and every aligned beta
  outcome of every direct reduct is computable (map row B2).
* `LambdaFactFromReducts` — the lambda fact follows from its function-side half (map row B7
  reduced to `LambdaReducts`).
* `TypedComputabilityFromRows` — the closing split: `TypedCarrierComputability A c` follows from
  the four open rows below.

Open rows (named, **not asserted**):

* `NeutralReducts A c` — every direct reduct of a typed non-lambda carrier is computable at its
  type. Contains the bound-variable step law, application decoding, the constructor induction (L)
  and their use inside the structural induction (map rows N4, D1–D4, H1–H3, S1).
* `GroundNotLambda A c` — no typed carrier of ground type fails the neutral test.
* `LambdaReducts A L₀ U c` — the direct reducts of a typed lambda carrier whose instances are
  computable are computable at the arrow type (map rows B5, B6, B8 with N7).
* `LambdaInstances A L₀ U c` — the instance premise itself: every aligned beta outcome of a
  typed lambda carrier at a computable argument is computable (the structural induction under
  computable substitution, map row S1).

Not claimed: any of the four open rows, `TypedCarrierComputability`, `AllTerms`,
`lem:arithmetic-accessibility`. The "lambda" class is stated as failure of the neutral test
(`(atom neutralSource x).not`), which for an address shell is the lambda header; deriving the
positive lambda shape from it is part of the open rows. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneTypedRowsTargetsV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (carrier)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (accepts formula)
open NumberedWindowInternalNeutralFactsTargets (D FactsAt atom direct reducts)
open NumberedWindowInternalLiteralNeutralAtomProof (neutralSource)
open NumberedWindowInternalAtomicRefinement (bottomSource freeSource)
open NumberedWindowInternalProbeTargets (typedAt)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeParsedTyped (chosenH)
open NumberedWindowInternalLiteralAddressedChildReportsProof (hop)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralConcreteBetaJoinedRulesProof (BetaJoinedRulesAt)
open NumberedWindowInternalLiteralJoinedBetaOutcomeProof (BetaOutcomeAt)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowOriginalComputabilityFormulaTargets (formulaType)
open Paper16AccessibilityMilestoneTargetsV2 (InstalledWindow TypedCarrierComputability)

variable {S : Spine.Signature} {K : List Ty} {W : List ProbeTy}

/-- The one-hop checker of the installed window. -/
abbrev windowHop (A : InstalledWindow S K W) : Program 3 :=
  hop A.contextGuard A.typeGuard
    (rawWithTarget A.scalar A.contextGuard A.typeGuard A.raw A.least) A.least

/-- The guarded application program built from the window's scalar and least programs. -/
abbrev windowApp (A : InstalledWindow S K W) : Program 3 :=
  applicationGuard A.scalar A.least

/-- The joined beta rules at the window's own programs. -/
abbrev JoinedAt (A : InstalledWindow S K W) (L₀ : Program 3) (U : Program 2) (c : Nat) : Prop :=
  BetaJoinedRulesAt A.presentation A.scalar (windowApp A) (windowHop A) L₀ A.least U W A.probes c

/-- N1–N3. The neutral lemma, bottoms and free variables, at every formula type. -/
def WindowNeutralFacts : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty) (W : List ProbeTy) (A : InstalledWindow S K W)
    (L₀ : Program 3) (U : Program 2) (c : Nat), JoinedAt A L₀ U c →
    ∀ τ : LogicLineages.OrdinalComparison.Source.Ty,
      FactsAt A.presentation (windowApp A) (windowHop A) neutralSource bottomSource freeSource c τ

/-- B2. Computability of an accepted application from its function's direct reducts, its
argument and its aligned beta outcomes. -/
def WindowBetaApplication : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty) (W : List ProbeTy) (A : InstalledWindow S K W)
    (L₀ : Program 3) (U : Program 2) (c : Nat), JoinedAt A L₀ U c →
    ∀ (σ τ : LogicLineages.OrdinalComparison.Source.Ty) (α : Type) (Γ : List (Formula α))
      (x u t : OTerm α),
      D A.presentation c Γ (accepts (windowApp A) x u t) →
      D A.presentation c Γ (reducts A.presentation (windowApp A) (windowHop A) c (.arrow σ τ) x) →
      D A.presentation c Γ (formula (windowApp A) σ u) →
      (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (y : OTerm β),
        (∀ f ∈ Γ, f.relabel j ∈ Δ) →
        D A.presentation c Δ (direct A.presentation (windowHop A) c (t.relabel j) y) →
        BetaOutcomeAt (sourceBody A.presentation c) Δ A.scalar L₀ A.least U
          (x.relabel j) (u.relabel j) y (formula (windowApp A) τ y)) →
      D A.presentation c Γ (formula (windowApp A) τ t)

/-- The instance premise of the lambda fact for the address `x` in the context `Γ`: in every
extension, for every computable argument `u`, accepted application `t` of `x` to `u` and direct
reduct `y` of `t`, the aligned beta outcomes of `y` are computable at the codomain. -/
def InstancesComputable (A : InstalledWindow S K W) (L₀ : Program 3) (U : Program 2) (c : Nat)
    (σ τ : LogicLineages.OrdinalComparison.Source.Ty) {α : Type} (Γ : List (Formula α))
    (x : OTerm α) : Prop :=
  ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (u t y : OTerm β),
    (∀ f ∈ Γ, f.relabel j ∈ Δ) →
    D A.presentation c Δ (formula (windowApp A) σ u) →
    D A.presentation c Δ (accepts (windowApp A) (x.relabel j) u t) →
    D A.presentation c Δ (direct A.presentation (windowHop A) c t y) →
    BetaOutcomeAt (sourceBody A.presentation c) Δ A.scalar L₀ A.least U
      (x.relabel j) u y (formula (windowApp A) τ y)

/-- Open row. The function-side half of the lambda fact: the direct reducts of a typed
non-neutral carrier whose instances are computable are computable at the arrow type. -/
def LambdaReducts (A : InstalledWindow S K W) (L₀ : Program 3) (U : Program 2) (c : Nat) : Prop :=
  ∀ (σ τ : LogicLineages.OrdinalComparison.Source.Ty) (α : Type) (Γ : List (Formula α))
    (x : OTerm α),
    D A.presentation c Γ (carrier A.presentation false c x) →
    D A.presentation c Γ (typedAt (chosenH A.probes W) (.arrow σ τ) x) →
    D A.presentation c Γ (atom neutralSource x).not →
    InstancesComputable A L₀ U c σ τ Γ x →
    D A.presentation c Γ (reducts A.presentation (windowApp A) (windowHop A) c (.arrow σ τ) x)

/-- The lambda fact: a typed non-neutral carrier whose instances are computable is computable
at the arrow type. -/
def LambdaFact (A : InstalledWindow S K W) (L₀ : Program 3) (U : Program 2) (c : Nat) : Prop :=
  ∀ (σ τ : LogicLineages.OrdinalComparison.Source.Ty) (α : Type) (Γ : List (Formula α))
    (x : OTerm α),
    D A.presentation c Γ (carrier A.presentation false c x) →
    D A.presentation c Γ (typedAt (chosenH A.probes W) (.arrow σ τ) x) →
    D A.presentation c Γ (atom neutralSource x).not →
    InstancesComputable A L₀ U c σ τ Γ x →
    D A.presentation c Γ (formula (windowApp A) (.arrow σ τ) x)

/-- B7 reduced to its function-side half. -/
def LambdaFactFromReducts : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty) (W : List ProbeTy) (A : InstalledWindow S K W)
    (L₀ : Program 3) (U : Program 2) (c : Nat), JoinedAt A L₀ U c →
    LambdaReducts A L₀ U c → LambdaFact A L₀ U c

/-- Open row. Every direct reduct of a typed neutral (non-lambda) carrier is computable at its
type. -/
def NeutralReducts (A : InstalledWindow S K W) (c : Nat) : Prop :=
  ∀ (τ : Ty) (_ : τ ∈ K) (α : Type) (Γ : List (Formula α)) (q : OTerm α),
    D A.presentation c Γ (carrier A.presentation false c q) →
    D A.presentation c Γ (typedAt (chosenH A.probes W) (formulaType τ) q) →
    D A.presentation c Γ (atom neutralSource q) →
    D A.presentation c Γ
      (reducts A.presentation (windowApp A) (windowHop A) c (formulaType τ) q)

/-- Open row. A carrier typed at the ground type passes the neutral test. -/
def GroundNotLambda (A : InstalledWindow S K W) (c : Nat) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (q : OTerm α),
    D A.presentation c Γ (carrier A.presentation false c q) →
    D A.presentation c Γ (typedAt (chosenH A.probes W) (formulaType .ground) q) →
    D A.presentation c Γ (atom neutralSource q).not →
    D A.presentation c Γ ⊥

/-- Open row. The instance premise holds for every typed non-neutral carrier of a listed arrow
type. -/
def LambdaInstances (A : InstalledWindow S K W) (L₀ : Program 3) (U : Program 2) (c : Nat) :
    Prop :=
  ∀ (σ τ : Ty), (.arrow σ τ : Ty) ∈ K → ∀ (α : Type) (Γ : List (Formula α)) (x : OTerm α),
    D A.presentation c Γ (carrier A.presentation false c x) →
    D A.presentation c Γ (typedAt (chosenH A.probes W) (formulaType (.arrow σ τ)) x) →
    D A.presentation c Γ (atom neutralSource x).not →
    InstancesComputable A L₀ U c (formulaType σ) (formulaType τ) Γ x

/-- The closing split. On a window with the guard equation and the joined rules,
`TypedCarrierComputability` follows from the four open rows. -/
def TypedComputabilityFromRows : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty) (W : List ProbeTy) (A : InstalledWindow S K W)
    (L₀ : Program 3) (U : Program 2) (c : Nat),
    A.probes.applicationGuard = applicationGuard A.scalar A.least → JoinedAt A L₀ U c →
    NeutralReducts A c → GroundNotLambda A c → LambdaReducts A L₀ U c →
    LambdaInstances A L₀ U c → TypedCarrierComputability A c

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneTypedRowsTargetsV2
