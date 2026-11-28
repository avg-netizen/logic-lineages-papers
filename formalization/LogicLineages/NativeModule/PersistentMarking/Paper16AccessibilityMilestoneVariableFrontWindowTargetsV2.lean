module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParser

/-! Frozen targets: a positive front test for free-variable nodes on the intrinsic window leaf
(K1 `FreshAddressCarrier`, step 2 of
`verification/local-fable-trio-2026-11-27/fableB2/K1-OBLIGATIONS-NOTE.md`; Fable B2,
27 November 2026).

The strict auxiliary window `strictAuxWindow base T` calls its leaf `base` on every row that is
not a tag-six auxiliary row, and `base` is a Primrec-realization witness of
`intrinsicWindow s ctx raw`. The legacy `namedGrammarBase` adds a rejection guard in front of it
and still returns `base` on acceptance. `variableFrontWindow T base` decides free-variable nodes
completely: on a node with header tag 0 and arity 2 it returns zero when the packed context does
not parse or the type program `T` rejects field 0, and the successor of field 0 otherwise; on
every other input it returns `base`.

The numeric content is `intrinsicWindow s ctx (packNode 0 [ty, i]) =
if (unpack ctx).isSome && typeGuard s ty then ty + 1 else 0`: for a free variable the lexical
requirement is empty, the annotation is field 0, and syntax and admission are the type guard.

* `VariableFrontWindowCalibrated` — the all-input calibration `IntrinsicWindowCalibrated` is
  preserved for a `TypeGuardCalibrated` type program.
* `OpenVariableFrontWindow` — the open-term law: at a term of free-variable shape, from a
  successful context parse and acceptance of the type field, the front window reports the
  successor of the type field.

Not claimed: the passage of this report through the memo `strictAuxIntrinsic` to
`windowGraph (strictAuxWindow …)`; any re-installation; K1. Bound names (tag 1) are not
intercepted. `branch control a b` is `a` on control zero, `b` otherwise. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneVariableFrontWindowTargetsV2

open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelope (field applyUnary)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw)
open NumberedWindowInternalAuxWindowMemoTargets (IntrinsicWindowCalibrated)
open NumberedWindowInternalAuxWindowStepTargets (TypeGuardCalibrated)

/-- The context parser on slot 0 of the leaf tape `[ctx, raw]`. -/
def contextParsed : Program 2 := .composition parser (fun _ : Fin 1 => .projection 0)

/-- The type program at field 0 of the raw key. -/
def variableGuard (T : Program 1) : Program 2 := onRaw (applyUnary T (field 0))

/-- The successor of field 0 of the raw key: the positive result code of the leaf. -/
def variableResult : Program 2 := onRaw (applyUnary .succ (field 0))

/-- The intrinsic window value at a free-variable node. -/
def variableWindowValue (T : Program 1) : Program 2 :=
  branch contextParsed (constantZero 2) (branch (variableGuard T) (constantZero 2) variableResult)

/-- The window leaf with free-variable nodes decided before the leaf is called. -/
def variableFrontWindow (T : Program 1) (base : Program 2) : Program 2 :=
  branch (onRaw (header 0 2)) base (variableWindowValue T)

/-- The front test preserves the all-input calibration of the window leaf. -/
def VariableFrontWindowCalibrated : Prop :=
  ∀ (s : Settings) (T : Program 1) (base : Program 2),
    TypeGuardCalibrated s T → IntrinsicWindowCalibrated s base →
    IntrinsicWindowCalibrated s (variableFrontWindow T base)

/-- At an open term of free-variable shape, a parsed context and an accepted type field give the
positive leaf report. Arbitrary leaf `base`, type program, body, context and open terms. -/
def OpenVariableFrontWindow : Prop :=
  ∀ (T : Program 1) (base : Program 2) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ctx ty i tag : OTerm α),
    Nonempty (Derivation body Γ (unary parser (suc tag) ctx)) →
    Nonempty (Derivation body Γ (unary T (suc z) ty)) →
    Nonempty (Derivation body Γ
      (programGraph (variableFrontWindow T base) (suc ty) ![ctx, namedTerm 0 ty i]))

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneVariableFrontWindowTargetsV2
