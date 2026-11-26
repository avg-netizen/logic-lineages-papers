module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredEnrichedLiftProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoApplicationTransportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredMemoTransportProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons suc z unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalSettingsGrammarGuardOpenProof (exact_OpenSettingsRefitGuardReports)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof (CanReverse)
open NumberedWindowInternalLiteralTypedMemoUnfoldingProof (recursiveTypedMemo)
open NumberedWindowInternalLiteralTypedMemoStageProof (typedMemoStage)
open NumberedWindowInternalLiteralTypedDualMemoProof (exact_OpenDualContextMemoBase)
open NumberedWindowInternalLiteralPackedLeastOnProof (leastOnGraph packedLeastOn)
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralMemoRoundApplicationMotiveProof (varyAuxiliary)
open NumberedWindowInternalLiteralMemoVaryingParentProof (varyingOperandType exact_MemoVaryingTypeRename BaseApplicationLiftAt)
open NumberedWindowInternalLiteralMemoApplicationTransportProof (exact_OpenTypedMemoApplicationTransport)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictCover)
open NumberedWindowInternalLiteralStrictMeasuredPlainLiftProof
open NumberedWindowInternalLiteralStrictMeasuredEnrichedLiftProof

attribute [local irreducible] programGraph recursiveTypedMemo packedLeastOn
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

abbrev selectedBiAuxType (s : Settings) (T TV : Program 1) := conjunction (refitGuard s T) TV

theorem exact_OpenBiAuxTypeEvidence (s : Settings) (T TV : Program 1) (dom cod : OTerm α)
    (hd : D B Γ (unary (selectedBiAuxType s T TV) (suc z) dom))
    (hc : D B Γ (unary (selectedBiAuxType s T TV) (suc z) cod)) :
    ParentTypeEvidence s (selectedBiAuxType s T TV) TV B Γ dom cod := by
  obtain ⟨p⟩ := conjunctionRecover (refitGuard s T) TV ![dom] hd
  obtain ⟨q⟩ := conjunctionRecover (refitGuard s T) TV ![cod] hc
  obtain ⟨d⟩ := exact_OpenSettingsRefitGuardReports s T B α Γ dom
  obtain ⟨c⟩ := exact_OpenSettingsRefitGuardReports s T B α Γ cod
  have fd := Derivation.implicationElimination (Derivation.conjunctionLeft d) (Derivation.conjunctionLeft p)
  have fc := Derivation.implicationElimination (Derivation.conjunctionLeft c) (Derivation.conjunctionLeft q)
  exact ⟨⟨Derivation.conjunctionIntroduction (Classical.choice hd) (Classical.choice hc)⟩,
    ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionRight p) (Derivation.conjunctionRight q)⟩,
    ⟨Derivation.conjunctionRight fd⟩,⟨Derivation.conjunctionRight fc⟩⟩

private theorem renameEvidence {β : Type} {Δ : List (Formula β)} (s : Settings) (T TV : Program 1)
    (dom cod : OTerm α) (j : α → β) (keep : ∀ p ∈ Γ, p.relabel j ∈ Δ)
    (given : ParentTypeEvidence s T TV B Γ dom cod) :
    ParentTypeEvidence s T TV B Δ (dom.relabel j) (cod.relabel j) := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [conjunctionRename,unaryRename,sucRelabel,zRelabel] using renameInto given.typed j Δ keep
  · simpa only [conjunctionRename,unaryRename,sucRelabel,zRelabel] using renameInto given.wellFormed j Δ keep
  · simpa only [graphRename,typesTerm,numeralRename] using renameInto given.domain j Δ keep
  · simpa only [graphRename,typesTerm,numeralRename] using renameInto given.codomain j Δ keep

theorem exact_OpenSelectedBiAuxBaseLiftAt (s : Settings) (X base : Program 2) (T V TV baseM : Program 1)
    (v : Bool) (ctx dom cod fixed : OTerm α)
    (types : ParentTypeEvidence s T TV B Γ dom cod)
    (arg : D B Γ (windowAt (selectedBiAuxWindow s base T V TV baseM) ctx
      (varyingOperandType (!v) dom cod) fixed)) :
    BaseApplicationLiftAt (selectedBiAuxBase s X base T V TV baseM) v B Γ ctx dom cod fixed := by
  intro β j Δ q r keep child
  let E := selectedBiAuxBase s X base T V TV baseM
  let c := ctx.relabel j
  let d := dom.relabel j
  let k := cod.relabel j
  let a := fixed.relabel j
  rw [recursiveTypedMemo] at child
  have baseChild := exact_OpenDualContextMemoBase E (typedMemoStage E) B β Δ c
    (varyingOperandType v d k) q r child
  have form := renameInto arg j Δ keep
  rw [windowRename,exact_MemoVaryingTypeRename] at form
  exact exact_OpenStrictMeasuredBaseLift s X base T V TV baseM v c d k q r a
    (renameEvidence s T TV dom cod j keep types) form baseChild

/-- The actual parent's least value can now be transported along either
selected child class without an external parent-edge hypothesis.
Only original fixed typed operand and original type guards are needed. -/
theorem exact_OpenStrictMeasuredMemoTransport (s : Settings) (X base : Program 2)
    (T V TV baseM : Program 1) (v : Bool) (ctx dom cod q k fixed m : OTerm α) :
    let C := measuredStrictCover V TV baseM
    let Base := selectedBiAuxBase s X base T V TV baseM
    let E := recursiveTypedMemo Base
    CanReverse Base → Preserves E (packedLeastOn C E s) →
    ParentTypeEvidence s T TV B Γ dom cod →
    D B Γ (windowAt (selectedBiAuxWindow s base T V TV baseM) ctx (varyingOperandType (!v) dom cod) fixed) →
    D B Γ (leastOnGraph C E s ctx (varyingOperandType v dom cod) q k) →
    D B Γ (leastOnGraph C E s ctx cod (varyAuxiliary v dom cod q fixed) m) →
    D B Γ (leastOnGraph C E s ctx cod (varyAuxiliary v dom cod k fixed) m) := by
  intro C Base E reverse stable types window child parent
  have lift := exact_OpenSelectedBiAuxBaseLiftAt s X base T V TV baseM v ctx dom cod fixed types window
  exact exact_OpenTypedMemoApplicationTransport C Base s reverse stable v ctx dom cod q k fixed m lift child parent

#print axioms exact_OpenBiAuxTypeEvidence
#print axioms exact_OpenSelectedBiAuxBaseLiftAt
#print axioms exact_OpenStrictMeasuredMemoTransport
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredMemoTransportProof
