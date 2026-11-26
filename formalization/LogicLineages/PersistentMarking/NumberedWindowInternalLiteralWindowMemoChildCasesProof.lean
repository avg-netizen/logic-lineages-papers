module
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoRowSupportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoLeastLawsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSealedWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoWindowSoundProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHeaderLeastOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictChildSelectionProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictOperandMinimaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralWindowMemoChildCasesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalOriginalFirstHopCoreProof (literalAddress)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalNeutralFactsTargets (direct)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (D finiteScalar)
open NumberedWindowInternalLiteralTypeMembershipTargets (literalMembership)
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn leastOnGraph)
open NumberedWindowInternalLiteralLeastOnFixedPointProof (WindowEndpoints)
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralEdgeObserversProof (withObservers)
open NumberedWindowInternalLiteralChildGuardEdgeProof (childGuardObservers)
open NumberedWindowInternalLiteralStrictSealedWindowProof (strictSealedWindow)
open NumberedWindowInternalLiteralEnrichedCanonicalChildProof (exact_OpenEnrichedCanonicalChild)
open NumberedWindowInternalLiteralLeastOnFixedPointProof (casesLeastOn)
open NumberedWindowInternalLiteralLeastOnCoverageProof (exact_OpenLeastOnFromCoverage)
open NumberedWindowInternalLiteralTypedMemoUnfoldingProof (recursiveTypedMemo)
open NumberedWindowInternalLiteralTypedMemoLeastLawsProof
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)
open NumberedWindowInternalLiteralSealedWindowProof (exact_OpenSealedWindow)
open NumberedWindowInternalLiteralSyntaxMemoWindowSoundProof (windowRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (exact_OpenAtomicLeastReport)
open NumberedWindowInternalLiteralHeaderLeastOpenProof (exact_OpenLiteralHeaderLeastReport)
open NumberedWindowInternalLiteralAuxProfileLeastOpenProof (exact_OpenLiteralAuxProfileLeastReport)
open NumberedWindowInternalLiteralAuxProfileLeastProof (auxProfileLeast)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof
  (fullAuxiliaryDecorator childGuardedLeast exact_OpenFullFilteredNonAuxLeast)
open NumberedWindowInternalLiteralCarrierChildHopProof (exact_OpenCarrierChildHopAtLeast)

open NumberedWindowInternalLiteralCoveredMemoRowSupportProof (coverageReport)

attribute [local irreducible] programGraph
variable {α : Type} {Γ : List (Formula α)}

private theorem literalMembershipRename {β : Type} (finite : List Nat) (ty : OTerm α) (j : α → β) :
    (literalMembership finite ty).relabel j = literalMembership finite (ty.relabel j) := by
  simp only [literalMembership,graphRename,numeralRename]

/-- The actual stored source report is read down to the original primitive
least graph, then restored with both class queries checked by the same
memo selector. The target comes from its real covered window. No restriction
on the shape of either raw child remains. -/
theorem exact_OpenWindowMemoChildCases (cv tv : Program 1) (C : Program 3) (Base : Program 4)
    (s : Settings) (W : Program 3) (raw : Program 5) (finite : List Nat) (c : Nat)
    (ctx ty seed witness target source : OTerm α) (goal : Formula α) :
    let E := recursiveTypedMemo Base
    let L₀ := packedLeastOn C E s
    let L := memoFilteredLeast C Base s
    let i := finiteScalar (addressScalar cv tv W L) finite
    let R := rawWithTarget i cv tv raw L
    let data := S i cv tv R L
    let B := sourceBody data c
    WindowEndpoints W E → Preserves E L₀ → MemoSelectedReports C s Base →
    D B Γ (unary cv (suc z) ctx) → D B Γ (unary tv (suc z) ty) →
    D B Γ (literalMembership finite ty) → D B Γ (windowAt W ctx ty target) →
    D B Γ (coverageReport C s ctx target) →
    D B Γ (programGraph raw (suc z) ![ctx,ty,seed,witness,target]) →
    D B Γ (programGraph (childGuardedLeast L₀) (suc source) ![ctx,ty,seed]) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (k : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (leastOnGraph C E s (ctx.relabel j) (ty.relabel j) (target.relabel j) k) →
      D B Δ (unary i (suc z) (literalAddress (ctx.relabel j) (ty.relabel j) k)) →
      D B Δ (direct data (hop cv tv R L) c
        (literalAddress (ctx.relabel j) (ty.relabel j) (source.relabel j))
        (literalAddress (ctx.relabel j) (ty.relabel j) k)) → D B Δ (goal.relabel j)) →
    D B Γ goal := by
  intro E L₀ L i R data B ends stable selected gc gt listed formed cover child sourceMin use
  obtain ⟨atomic⟩ := exact_OpenAtomicLeastReport (headerLeast (auxProfileLeast L₀)) ctx ty seed source sourceMin
  obtain ⟨header⟩ := exact_OpenLiteralHeaderLeastReport (auxProfileLeast L₀) ctx ty seed source
    ⟨Derivation.conjunctionLeft atomic⟩
  obtain ⟨profile⟩ := exact_OpenLiteralAuxProfileLeastReport L₀ ctx ty seed source
    ⟨Derivation.conjunctionLeft header⟩
  have left := selected B α Γ ctx ty seed source ⟨Derivation.conjunctionLeft profile⟩
  have least := exact_OpenLeastOnFromCoverage C E s ctx ty target cover
  apply casesLeastOn C E s ctx ty target goal least
  intro β j Δ k keep selectedTarget
  have l := renameInto left j Δ keep
  simp only [programRename,tripleInputsRename,sucRelabel] at l
  have cvt := renameInto gc j Δ keep
  have tvt := renameInto gt j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at cvt tvt
  have win := renameInto formed j Δ keep
  rw [show (windowAt W ctx ty target).relabel j = windowAt W (ctx.relabel j) (ty.relabel j) (target.relabel j) from windowRename W ctx ty target j] at win
  have supported := renameInto listed j Δ keep
  rw [literalMembershipRename] at supported
  have raw' := renameInto child j Δ keep
  simp only [NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof.graph5Rename,sucRelabel,zRelabel] at raw'
  let sc := ctx.relabel j
  let st := ty.relabel j
  let rd := target.relabel j
  have r := selected B β Δ sc st rd k selectedTarget
  have addr := exact_OpenEnrichedCanonicalChild cv tv C W E s finite sc st rd k ends stable cvt tvt
    supported win selectedTarget
  have called := exact_OpenCarrierChildHopAtLeast i cv tv raw L c sc st (seed.relabel j)
    (witness.relabel j) rd (source.relabel j) k cvt tvt raw' l r addr
  exact use β j Δ k keep selectedTarget addr called

#print axioms exact_OpenWindowMemoChildCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralWindowMemoChildCasesProof
