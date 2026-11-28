module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedAllApplicationCasesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaOperandAlignmentProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedBetaOutcomeRepairCheckProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ChildClosed)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs)
open NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof (inputsRename)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof (CanReverse)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (finiteCodes finiteScalar)
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn)
open NumberedWindowInternalLiteralLeastOnFixedPointProof (WindowEndpoints)
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictCover)
open NumberedWindowInternalLiteralStrictMeasuredMemoTransportProof (selectedBiAuxType)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)
open NumberedWindowInternalLiteralTypedMemoUnfoldingProof (recursiveTypedMemo)
open NumberedWindowInternalLiteralTypedMemoLeastLawsProof (memoFilteredLeast MemoSelectedReports)
open NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof (joinedAuxiliaryWindow)
open NumberedWindowInternalLiteralBiAuxBaseWindowLiftProof (joinedBiAuxBase)
open NumberedWindowInternalLiteralJoinedRawFunctionLiftProof (selectedJoinedRaw)
open NumberedWindowInternalLiteralRankForwardRowsProof (OpenRankTypeGuards)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalNeutralFactsTargets (atom direct inherited)
open NumberedWindowInternalAtomicRefinement (bottomSource)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalLiteralBetaLeafProof (withBetaLeaf)
open NumberedWindowInternalLiteralJoinedAllApplicationCasesProof (exact_OpenJoinedAllApplicationCases)
open NumberedWindowInternalLiteralAddressedBetaInstanceProof (exact_OpenAddressedBetaInstance)
open NumberedWindowInternalLiteralBetaOperandAlignmentProof (AlignedBetaRow exact_OpenAlignedBetaRow)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof (fullAuxiliaryDecorator)

attribute [local irreducible] programGraph recursiveTypedMemo packedLeastOn direct
variable {α : Type} {Γ : List (Formula α)}

/-- Tightly scoped remaining obligation at each physical beta outcome.
Only the aligned raw instance and the exact original addressed target
are passed to the continuation, and both original operands are still
checked. -/
def BetaOutcomeAt {α : Type} (B : Positive (Fin 1)) (Γ : List (Formula α))
    (i : Program 1) (L₀ L : Program 3) (U : Program 2) (x u y : OTerm α)
    (goal : Formula α) : Prop :=
  ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
    (ctx result dom cod fn arg sc st after q r d e f a bind body : OTerm β),
    (∀ φ ∈ Γ, φ.relabel j ∈ Δ) →
    D B Δ (unary i (suc z) (x.relabel j)) →
    D B Δ (unary i (suc z) (u.relabel j)) →
    D B Δ (parsedApplicationInputs (x.relabel j) (u.relabel j) ctx result dom cod fn arg) →
    AlignedBetaRow L₀ L U B Δ ctx dom cod fn arg sc st after q r d e f a bind body (y.relabel j) →
    D B Δ (goal.relabel j)

/-- The aligned beta outcome with the original output type equation retained
in the same context as the parsed operands and aligned row. -/
def BetaOutcomeWithTypeAt {α : Type} (B : Positive (Fin 1)) (Γ : List (Formula α))
    (i : Program 1) (L₀ L : Program 3) (U : Program 2) (x u y : OTerm α)
    (goal : Formula α) : Prop :=
  ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
    (ctx result dom cod fn arg sc st after q r d e f a bind body : OTerm β),
    (∀ φ ∈ Γ, φ.relabel j ∈ Δ) →
    D B Δ (unary i (suc z) (x.relabel j)) →
    D B Δ (unary i (suc z) (u.relabel j)) →
    D B Δ (parsedApplicationInputs (x.relabel j) (u.relabel j) ctx result dom cod fn arg) →
    D B Δ (eqn st cod) →
    AlignedBetaRow L₀ L U B Δ ctx dom cod fn arg sc st after q r d e f a bind body (y.relabel j) →
    D B Δ (goal.relabel j)

theorem exact_OpenJoinedBetaOutcomeWithType (s : Settings) (P : List ProbeTy) (closed : ChildClosed P)
    (X base U : Program 2) (T V baseM cv tv : Program 1)
    (leaves : Nat → Program 3) (other : Program 3) (c : Nat) (x u t y : OTerm α) (goal : Formula α) :
    let Tg := selectedBiAuxType s T tv
    let Va := unitAuxSyntax V tv
    let C := measuredStrictCover V tv baseM
    let W := joinedAuxiliaryWindow s base Tg V tv baseM
    let Base := joinedBiAuxBase s X base Tg V tv baseM
    let E := recursiveTypedMemo Base
    let L₀ := packedLeastOn C E s
    let L := memoFilteredLeast C Base s
    let i := finiteScalar (addressScalar cv tv W L) (finiteCodes P)
    let leaf := withBetaLeaf Va U leaves
    let raw := selectedJoinedRaw s base Tg V tv baseM leaf other
    let R := rawWithTarget i cv tv raw L
    let data := S i cv tv R L
    let H := hop cv tv R L
    let B := sourceBody data c
    CanReverse Base → WindowEndpoints W E → Preserves E L₀ → MemoSelectedReports C s Base →
    OpenRankTypeGuards P Tg tv →
    D B Γ (accepts (applicationGuard i L) x u t) →
    D B Γ (direct data H c t y) →
    BetaOutcomeWithTypeAt B Γ i L₀ L U x u y goal →
    D B Γ (atom bottomSource y ⊔ (inherited data (applicationGuard i L) H c x u y ⊔ goal)) := by
  intro Tg Va C W Base E L₀ L i leaf raw R data H B reverse ends stable selected types app step pay
  apply exact_OpenJoinedAllApplicationCases s P closed X base T V baseM cv tv leaf other c x u t y goal
    reverse ends stable selected types app step
  intro β j Δ ctx result dom cod fn arg k sc st before after cert q w r payload
    keep left right parsed address scope outputType _ parent _ root _ calls
  apply exact_OpenAddressedBetaInstance Va U leaves R L (y.relabel j) sc st before after cert q w r payload
    (goal.relabel j) address calls root
  intro γ n Θ d e f a bind body stay source head domTy selectedRun rawLeft rawRight target
  let m := n ∘ j
  have keepM (p : Formula α) (used : p ∈ Γ) : p.relabel m ∈ Θ := by
    simpa only [m,formulaRelabelComposition] using stay _ (keep p used)
  have fa := renameInto left n Θ stay
  have ua := renameInto right n Θ stay
  simp only [unaryRename,sucRelabel,zRelabel,Term.relabel_relabel] at fa ua
  have p := renameInto parsed n Θ stay
  simp only [inputsRename,Term.relabel_relabel] at p
  have same := renameInto scope n Θ stay
  have sameType := renameInto outputType n Θ stay
  rw [eqnRelabel] at same sameType
  have fromApp := renameInto parent n Θ stay
  simp only [programRename,tripleInputsRename,sucRelabel,auxiliaryRename] at fromApp
  let actualLeast := guardedLeast (headerLeast (fullAuxiliaryDecorator L₀))
  have leastEq : actualLeast = L := rfl
  let actualScalar := finiteScalar (addressScalar cv tv W actualLeast) (finiteCodes P)
  have scalarEq : actualScalar = i := by unfold actualScalar i; rw [leastEq]
  have fa' : D B Θ (unary actualScalar (suc z) (x.relabel m)) := by
    rw [scalarEq]
    exact fa
  have ua' : D B Θ (unary actualScalar (suc z) (u.relabel m)) := by
    rw [scalarEq]
    exact ua
  have aRun := exact_OpenAlignedBetaRow cv tv W L₀ U (finiteCodes P) (x.relabel m) (u.relabel m)
    ((y.relabel j).relabel n) (ctx.relabel n) (result.relabel n) (dom.relabel n) (cod.relabel n) (fn.relabel n)
    (arg.relabel n) (sc.relabel n) (st.relabel n) (before.relabel n) (after.relabel n) (q.relabel n) (r.relabel n)
    d e f a bind body fa' ua' p same fromApp rawLeft source head domTy selectedRun rawRight target
  change AlignedBetaRow L₀ actualLeast U B Θ (ctx.relabel n) (dom.relabel n) (cod.relabel n) (fn.relabel n) (arg.relabel n)
    (sc.relabel n) (st.relabel n) (after.relabel n) (q.relabel n) (r.relabel n) d e f a bind body ((y.relabel j).relabel n) at aRun
  rw [leastEq] at aRun
  have done := pay γ m Θ (ctx.relabel n) (result.relabel n) (dom.relabel n) (cod.relabel n) (fn.relabel n) (arg.relabel n)
    (sc.relabel n) (st.relabel n) (after.relabel n) (q.relabel n) (r.relabel n) d e f a bind body keepM
    (by simpa only [m,Term.relabel_relabel] using fa)
    (by simpa only [m,Term.relabel_relabel] using ua)
    (by simpa only [m,Term.relabel_relabel] using p)
    sameType
    (by simpa only [m,Term.relabel_relabel] using aRun)
  simpa only [m,formulaRelabelComposition] using done

/-- The original aligned beta outcome interface follows by discarding the
output type equation. -/
theorem exact_OpenJoinedBetaOutcome (s : Settings) (P : List ProbeTy) (closed : ChildClosed P)
    (X base U : Program 2) (T V baseM cv tv : Program 1)
    (leaves : Nat → Program 3) (other : Program 3) (c : Nat) (x u t y : OTerm α) (goal : Formula α) :
    let Tg := selectedBiAuxType s T tv
    let Va := unitAuxSyntax V tv
    let C := measuredStrictCover V tv baseM
    let W := joinedAuxiliaryWindow s base Tg V tv baseM
    let Base := joinedBiAuxBase s X base Tg V tv baseM
    let E := recursiveTypedMemo Base
    let L₀ := packedLeastOn C E s
    let L := memoFilteredLeast C Base s
    let i := finiteScalar (addressScalar cv tv W L) (finiteCodes P)
    let leaf := withBetaLeaf Va U leaves
    let raw := selectedJoinedRaw s base Tg V tv baseM leaf other
    let R := rawWithTarget i cv tv raw L
    let data := S i cv tv R L
    let H := hop cv tv R L
    let B := sourceBody data c
    CanReverse Base → WindowEndpoints W E → Preserves E L₀ → MemoSelectedReports C s Base →
    OpenRankTypeGuards P Tg tv →
    D B Γ (accepts (applicationGuard i L) x u t) →
    D B Γ (direct data H c t y) →
    BetaOutcomeAt B Γ i L₀ L U x u y goal →
    D B Γ (atom bottomSource y ⊔ (inherited data (applicationGuard i L) H c x u y ⊔ goal)) := by
  intro Tg Va C W Base E L₀ L i leaf raw R data H B reverse ends stable selected types app step pay
  apply exact_OpenJoinedBetaOutcomeWithType s P closed X base U T V baseM cv tv leaves other c x u t y goal
    reverse ends stable selected types app step
  intro β j Δ ctx result dom cod fn arg sc st after q r d e f a bind body keep left right parsed _ row
  exact pay β j Δ ctx result dom cod fn arg sc st after q r d e f a bind body keep left right parsed row

#print axioms BetaOutcomeAt
#print axioms BetaOutcomeWithTypeAt
#print axioms exact_OpenJoinedBetaOutcomeWithType
#print axioms exact_OpenJoinedBetaOutcome
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedBetaOutcomeRepairCheckProof
