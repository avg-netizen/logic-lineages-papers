module

public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterObjectTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicLeastGuardProof

/-! Frozen targets: two facts about the payload of the fresh address that
`verification/local-fable-trio-2026-11-27/fableB2/K1-OBLIGATIONS-NOTE.md` recorded as read but
not derived (K1 `FreshAddressCarrier`; Fable B2, 27 November 2026; root's order to compile both
before the packet restatement).

* `FreshPayloadIsNamedLeaf` — the packed free address is the literal address whose least field
  is the named leaf `namedTerm 0 dom name` of the legacy named-leaf line.
* `FreeSeedSelfLeast` — for every program `L`, a successor report of `guardedLeast L` at a
  free-variable seed is the seed itself. The installed least is `guardedLeast (…)`, so the
  self-least of the fresh payload follows from the existence of any least; no fact about the
  edge program or its exchange leaf enters.

Not claimed: that a least exists at the payload (that needs coverage), nor K1. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFreshPayloadTargetsV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (packedFreeTerm)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)

/-- The packed free address is the literal address of a named leaf with tag zero. -/
def FreshPayloadIsNamedLeaf : Prop :=
  ∀ (α : Type) (ctx dom name : OTerm α),
    packedFreeTerm ctx dom name = addressTerm ctx dom (namedTerm 0 dom name)

/-- A guarded least report at a free-variable seed selects the seed. Arbitrary inner program. -/
def FreeSeedSelfLeast : Prop :=
  ∀ (L : Program 3) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx ty a n t : OTerm α),
    Nonempty (Derivation body Γ
      (programGraph (guardedLeast L) (suc t) ![ctx, ty, namedTerm 0 a n])) →
    Nonempty (Derivation body Γ (eqn (namedTerm 0 a n) t))

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFreshPayloadTargetsV2
