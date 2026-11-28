module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredScratchProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoRowSupportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafMeasureTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameDefinitions

/-! Frozen targets: the installed memo programs at a free-variable leaf (K1
`FreshAddressCarrier`, step 4 of
`verification/local-fable-trio-2026-11-27/fableB2/K1-OBLIGATIONS-NOTE.md`; Fable B2,
27 November 2026).

The installed syntax, measure and covered-window programs are memo recursions that call their
leaf on every row that is not a tag-six auxiliary row. These four laws carry a leaf fact through
the memo at such a row.

* `NamedLeafUnitSyntax` — acceptance of a free-variable leaf by the syntax leaf `V` gives its
  acceptance by `unitAuxSyntax V TV`.
* `NamedLeafChosenMeasure` — the installed measure `chosenMeasure (namedMeasureBase M)` at a
  free-variable leaf is the pair `(1, i)` of the legacy measure front.
* `NamedLeafOwnCover` — a free-variable leaf with a listed type, accepted by the installed syntax
  program, occurs in its own scratch pool under the installed cover with the measure front.
* `NonAuxCoveredWindow` — at a key that rejects the auxiliary shape, a positive leaf report, the
  syntax bit and the coverage report give the covered memo window.

Not claimed: the leaf facts themselves; K1. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneNamedLeafMemoTargetsV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverNamedLeafMeasureTargets (namedMeasureBase)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredTargets (chosenMeasure)
open NumberedWindowInternalLiteralCoveredMemo (coveredMemoWindow)
open NumberedWindowInternalLiteralCoveredMemoRowSupportProof (coverageReport)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictCover)

/-- The installed syntax program accepts a free-variable leaf that its leaf program accepts. -/
def NamedLeafUnitSyntax : Prop :=
  ∀ (V TV : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ty i : OTerm α),
    Nonempty (Derivation body Γ (unary V (suc z) (namedTerm 0 ty i))) →
    Nonempty (Derivation body Γ (unary (unitAuxSyntax V TV) (suc z) (namedTerm 0 ty i)))

/-- The installed measure over the named-leaf front, at a free-variable leaf. -/
def NamedLeafChosenMeasure : Prop :=
  ∀ (M : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ty i p : OTerm α),
    Nonempty (Derivation body Γ
      (unary (chosenMeasure (namedMeasureBase M)) p (namedTerm 0 ty i))) →
    Nonempty (Derivation body Γ (codePair p (suc z) i))

/-- A free-variable leaf of a listed type, accepted by the installed syntax program, occurs in
its own scratch pool under the installed cover. -/
def NamedLeafOwnCover : Prop :=
  ∀ (V TV M : Program 1) (s : Settings) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ty i vertices : OTerm α),
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)) →
    Nonempty (Derivation body Γ (unary (unitAuxSyntax V TV) (suc z) (namedTerm 0 ty i))) →
    Nonempty (Derivation body Γ
      (unary (scratchVertices (measuredStrictCover V TV (namedMeasureBase M)) s) vertices
        (namedTerm 0 ty i))) →
    Nonempty (Derivation body Γ (memberGraph vertices (namedTerm 0 ty i)))

/-- The covered memo window at a key that rejects the auxiliary shape. -/
def NonAuxCoveredWindow : Prop :=
  ∀ (C : Program 3) (s : Settings) (A : Program 2) (T V : Program 1)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx prior result : OTerm α),
    Nonempty (Derivation body Γ (unary termShape z (suc prior))) →
    Nonempty (Derivation body Γ (programGraph A (suc result) ![ctx, suc prior])) →
    Nonempty (Derivation body Γ (unary V (suc z) (suc prior))) →
    Nonempty (Derivation body Γ (coverageReport C s ctx (suc prior))) →
    Nonempty (Derivation body Γ
      (windowGraph (coveredMemoWindow C s A T V) ctx result (suc prior)))

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneNamedLeafMemoTargetsV2
