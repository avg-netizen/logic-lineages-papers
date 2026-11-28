module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSyntaxRowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesTargets

/-! Frozen targets: a visible front test for free-variable nodes on the raw term syntax leaf
(K1 `FreshAddressCarrier`, repair step 1, syntax leaf only; Fable B2, 27 November 2026;
`verification/local-fable-trio-2026-11-27/root/K1-VARIABLE-NODE-FINDING.md`).

The installed syntax program `unitAuxSyntax V TV` calls its leaf `V` on every row that is not a
tag-six auxiliary row, and `V` is a Primrec-realization witness: at an open free-variable node
its value is not derivable. `variableFrontSyntax TV V` decides free-variable nodes before the
leaf is called: on a node with header tag 0 and arity 2 it returns the type program `TV` at
field 0, on every other input it returns `V`.

* `VariableSyntaxBit` — the numeric fact about the functions: on a free-variable node the term
  bit of `syntaxBits` is the type bit of field 0, which is what `variableCheck TV` computes for a
  calibrated `TV`.
* `VariableFrontSyntaxCalibrated` — all-input calibration is preserved, which is the only
  property downstream theorems ask of the leaf.
* `OpenVariableFrontSyntax` — the open-term law the front test exists for: at a term of
  free-variable shape, the graph of the front syntax is the graph of `TV` at the type field.

Not claimed: any re-installation of the packet or the window at `variableFrontSyntax TV V`;
the corresponding front tests for the measure and window leaves; K1. Bound names (tag 1) are
not intercepted. Note the argument order of `branch control a b`: `a` on control zero, `b`
otherwise. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneVariableFrontSyntaxTargetsV2

open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowInternalAuxExchangeMemoStepTargets (TermSyntaxCalibrated)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (TypeSyntaxCalibrated)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalSparsePathEnvelope (run field applyUnary)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)

/-- The explicit header test of a free-variable node: tag 0 with two fields (type, name). -/
abbrev isVariableNode : Program 1 := header 0 2

/-- The type program at field 0 of the current node. -/
def variableCheck (TV : Program 1) : Program 1 := applyUnary TV (field 0)

/-- The syntax leaf with free-variable nodes decided before the leaf is called. -/
def variableFrontSyntax (TV V : Program 1) : Program 1 :=
  branch isVariableNode V (variableCheck TV)

/-- On a free-variable node the term bit is what the variable check computes. -/
def VariableSyntaxBit : Prop :=
  ∀ TV : Program 1, TypeSyntaxCalibrated TV → ∀ raw : Nat,
    run isVariableNode raw = 1 → run (variableCheck TV) raw = (syntaxBits raw).1.toNat

/-- The front test preserves the all-input calibration of the syntax leaf. -/
def VariableFrontSyntaxCalibrated : Prop :=
  ∀ TV V : Program 1, TypeSyntaxCalibrated TV → TermSyntaxCalibrated V →
    TermSyntaxCalibrated (variableFrontSyntax TV V)

/-- At an open term of free-variable shape, the front syntax reports whatever the type program
reports at the type field. Arbitrary leaf `V`, type program, body, context and open terms. -/
def OpenVariableFrontSyntax : Prop :=
  ∀ (TV V : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ty i out : OTerm α),
    Nonempty (Derivation body Γ (unary TV out ty)) →
    Nonempty (Derivation body Γ (unary (variableFrontSyntax TV V) out (namedTerm 0 ty i)))

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneVariableFrontSyntaxTargetsV2
