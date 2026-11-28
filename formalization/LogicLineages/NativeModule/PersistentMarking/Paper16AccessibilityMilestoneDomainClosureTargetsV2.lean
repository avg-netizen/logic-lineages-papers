module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteScalarGuardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypeMembershipTargets

/-! Frozen targets: domain closure of the finite type window (K1 `FreshAddressCarrier`, step 1 of
`verification/local-fable-trio-2026-11-27/fableB2/K1-OBLIGATIONS-NOTE.md`; Fable B2,
27 November 2026).

The fresh address selected for an admitted address of type `σ → τ` stores the type `σ`. Its
finite scalar filter needs the literal membership of the code of `σ` in the window codes.
`ChildClosed` and `exact_OpenLiteralFiniteCodomain` give this for the codomain only.

* `DomainClosed W` — the window contains the domain of each of its arrow types.
* `OriginalWindowDomain` — the source window of a closed universe is domain-closed (numeric).
* `OpenLiteralFiniteDomain` — the open law: from literal membership of an arrow code
  `rawCons dom cod` in the codes of a domain-closed window, literal membership of `dom`.

Not claimed: anything about the fresh address itself. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneDomainClosureTargetsV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets (sourceWindow)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (finiteCodes)
open NumberedWindowInternalLiteralTypeMembershipTargets (literalMembership)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)

/-- The window contains the domain of each of its arrow types. -/
def DomainClosed (W : List ProbeTy) : Prop :=
  ∀ (σ τ : ProbeTy), LogicLineages.OrdinalComparison.Source.Ty.arrow σ τ ∈ W → σ ∈ W

/-- The source window of a closed universe is domain-closed. -/
def OriginalWindowDomain : Prop :=
  ∀ (K : List Ty), DecisionSourceUniverse.Closed K → DomainClosed (sourceWindow K)

/-- At an arrow code in the finite codes of a domain-closed window, the domain code is in the
same finite codes. Arbitrary body, context and open terms. -/
def OpenLiteralFiniteDomain : Prop :=
  ∀ (P : List ProbeTy), DomainClosed P →
    ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (dom cod : OTerm α),
      Nonempty (Derivation B Γ (literalMembership (finiteCodes P) (rawCons dom cod))) →
      Nonempty (Derivation B Γ (literalMembership (finiteCodes P) dom))

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneDomainClosureTargetsV2
