module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxBaseWindowLiftProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNormalizedAuxSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoApplicationTransportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxMemoTransportProof
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
open NumberedWindowInternalLiteralBiAuxBaseWindowLiftProof
open NumberedWindowInternalLiteralBiAuxWindowLiftProof (AuxWindowAssembly)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)

attribute [local irreducible] programGraph recursiveTypedMemo packedLeastOn
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem renameEvidence {β : Type} {Δ : List (Formula β)} (s : Settings) (T TV : Program 1)
    (dom cod : OTerm α) (j : α → β) (keep : ∀ p ∈ Γ, p.relabel j ∈ Δ)
    (given : ParentTypeEvidence s T TV B Γ dom cod) :
    ParentTypeEvidence s T TV B Δ (dom.relabel j) (cod.relabel j) := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [conjunctionRename,unaryRename,sucRelabel,zRelabel] using renameInto given.typed j Δ keep
  · simpa only [conjunctionRename,unaryRename,sucRelabel,zRelabel] using renameInto given.wellFormed j Δ keep
  · simpa only [graphRename,typesTerm,numeralRename] using renameInto given.domain j Δ keep
  · simpa only [graphRename,typesTerm,numeralRename] using renameInto given.codomain j Δ keep

theorem exact_OpenBiAuxBaseLiftAt (s : Settings) (X : Program 2) (T V TV baseM : Program 1)
    (W : Program 3) (assembly : AuxWindowAssembly s T TV (unitAuxSyntax V TV) W)
    (v : Bool) (ctx dom cod fixed : OTerm α)
    (types : ParentTypeEvidence s T TV B Γ dom cod)
    (arg : D B Γ (windowAt W ctx
      (varyingOperandType (!v) dom cod) fixed)) :
    BaseApplicationLiftAt (biAuxBaseOn s X V TV baseM W) v B Γ ctx dom cod fixed := by
  intro β j Δ q r keep child
  let E := biAuxBaseOn s X V TV baseM W
  let c := ctx.relabel j
  let d := dom.relabel j
  let k := cod.relabel j
  let a := fixed.relabel j
  rw [recursiveTypedMemo] at child
  have baseChild := exact_OpenDualContextMemoBase E (typedMemoStage E) B β Δ c
    (varyingOperandType v d k) q r child
  have form := renameInto arg j Δ keep
  rw [windowRename,exact_MemoVaryingTypeRename] at form
  exact exact_OpenBiAuxBaseWindowLift s X T V TV baseM W assembly v c d k q r a
    (renameEvidence s T TV dom cod j keep types) form baseChild

/-- The actual parent's least value can now be transported along either
selected child class without an external parent-edge hypothesis.
Only original fixed typed operand and original type guards are needed. -/
theorem exact_OpenBiAuxMemoTransport (s : Settings) (X : Program 2)
    (T V TV baseM : Program 1) (W : Program 3)
    (assembly : AuxWindowAssembly s T TV (unitAuxSyntax V TV) W) (v : Bool) (ctx dom cod q k fixed m : OTerm α) :
    let C := measuredStrictCover V TV baseM
    let Base := biAuxBaseOn s X V TV baseM W
    let E := recursiveTypedMemo Base
    CanReverse Base → Preserves E (packedLeastOn C E s) →
    ParentTypeEvidence s T TV B Γ dom cod →
    D B Γ (windowAt W ctx (varyingOperandType (!v) dom cod) fixed) →
    D B Γ (leastOnGraph C E s ctx (varyingOperandType v dom cod) q k) →
    D B Γ (leastOnGraph C E s ctx cod (varyAuxiliary v dom cod q fixed) m) →
    D B Γ (leastOnGraph C E s ctx cod (varyAuxiliary v dom cod k fixed) m) := by
  intro C Base E reverse stable types window child parent
  have lift := exact_OpenBiAuxBaseLiftAt s X T V TV baseM W assembly v ctx dom cod fixed types window
  exact exact_OpenTypedMemoApplicationTransport C Base s reverse stable v ctx dom cod q k fixed m lift child parent

#print axioms exact_OpenBiAuxBaseLiftAt
#print axioms exact_OpenBiAuxMemoTransport
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxMemoTransportProof
