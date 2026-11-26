module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredCanonicalImageProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictImageAlignmentProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralInheritedApplicationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicAddressReportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredInheritedImageProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel eqnRelabel)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseAddressPositiveOpenBindingProof (addressReportRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalLiteralAtomicAddressReportProof (renameAddress)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof (CanReverse)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (finiteScalar)
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn leastOnGraph)
open NumberedWindowInternalLiteralLeastOnFixedPointProof (WindowEndpoints)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictCover)
open NumberedWindowInternalLiteralStrictMeasuredPlainLiftProof
open NumberedWindowInternalLiteralStrictMeasuredEnrichedLiftProof
open NumberedWindowInternalLiteralTypedMemoUnfoldingProof (recursiveTypedMemo)
open NumberedWindowInternalLiteralTypedMemoLeastLawsProof (memoFilteredLeast MemoSelectedReports)
open NumberedWindowInternalLiteralStrictMeasuredImageTransportProof (exact_OpenStrictMeasuredCanonicalImage)
open NumberedWindowInternalLiteralStrictMeasuredCanonicalImageProof (exact_OpenStrictMeasuredReportedApplication)
open NumberedWindowInternalLiteralStrictImageAlignmentProof (StrictImageAligned)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalNeutralFactsTargets (direct inherited)
open NumberedWindowInternalLiteralInheritedApplicationProof (exact_OpenInheritedApplicationIntro exact_OriginalApplicationAcceptedGraph)
open NumberedWindowComputabilityFormulaTargets (accepts)

attribute [local irreducible] programGraph recursiveTypedMemo packedLeastOn direct
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem renameStrictImageAligned {β : Type} {Δ : List (Formula β)} (s : Settings)
    (T TV : Program 1) (L₀ : Program 3) (sc d e g a arg u y after : OTerm α) (j : α → β)
    (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    (given : StrictImageAligned s T TV L₀ B Γ sc d e g a arg u y after) :
    StrictImageAligned s T TV L₀ B Δ (sc.relabel j) (d.relabel j) (e.relabel j)
      (g.relabel j) (a.relabel j) (arg.relabel j) (u.relabel j) (y.relabel j) (after.relabel j) := by
  have types : ParentTypeEvidence s T TV B Δ (d.relabel j) (e.relabel j) := by
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [conjunctionRename,unaryRename,sucRelabel,zRelabel] using renameInto given.types.typed j Δ keep
    · simpa only [conjunctionRename,unaryRename,sucRelabel,zRelabel] using renameInto given.types.wellFormed j Δ keep
    · simpa only [graphRename,typesTerm,numeralRename] using renameInto given.types.domain j Δ keep
    · simpa only [graphRename,typesTerm,numeralRename] using renameInto given.types.codomain j Δ keep
  refine ⟨types,?_,?_,?_,?_⟩
  · simpa only [programRename,tripleInputsRename,sucRelabel] using renameInto given.argLeast j Δ keep
  · simpa only [programRename,tripleInputsRename,sucRelabel,auxiliaryRename] using renameInto given.goalLeast j Δ keep
  · simpa only [addressReportRename] using renameInto given.argument j Δ keep
  · simpa only [eqnRelabel,renameAddress] using renameInto given.result j Δ keep

/-- The same original argument and the same certified result are used
to construct the inherited application on a genuine selected direct
function child. The argument movement is entirely class transport. -/
theorem exact_OpenStrictMeasuredInheritedImage (s : Settings) (X base : Program 2)
    (T V TV baseM cv tv : Program 1) (raw : Program 5) (finite : List Nat) (c : Nat)
    (x u y sc d e g a arg gmin after : OTerm α) :
    let C := measuredStrictCover V TV baseM
    let W := selectedBiAuxWindow s base T V TV baseM
    let Base := selectedBiAuxBase s X base T V TV baseM
    let E := recursiveTypedMemo Base
    let L₀ := packedLeastOn C E s
    let L := memoFilteredLeast C Base s
    let i := finiteScalar (addressScalar cv tv W L) finite
    let R := rawWithTarget i cv tv raw L
    let data := S i cv tv R L
    let H := hop cv tv R L
    let B := sourceBody data c
    CanReverse Base → WindowEndpoints W E → Preserves E L₀ → MemoSelectedReports C s Base →
    StrictImageAligned s T TV L₀ B Γ sc d e g a arg u y after →
    D B Γ (windowAt W sc (rawCons d e) g) → D B Γ (windowAt W sc d a) →
    D B Γ (leastOnGraph C E s sc (rawCons d e) g gmin) →
    D B Γ (unary i (suc z) (addressTerm sc (rawCons d e) gmin)) →
    D B Γ (unary i (suc z) u) →
    D B Γ (direct data H c x (addressTerm sc (rawCons d e) gmin)) →
    D B Γ (inherited data (applicationGuard i L) H c x u y) := by
  intro C W Base E L₀ L i R data H B reverse ends stable selected held fW aW least fScalar uScalar step
  have image := exact_OpenStrictMeasuredCanonicalImage s X base T V TV baseM sc d e g a gmin arg after
    reverse ends stable held.types fW aW least held.argLeast held.goalLeast
  have rebuilt := exact_OpenStrictMeasuredReportedApplication s X base T V TV baseM cv tv finite
    sc d e gmin arg u y after selected image fScalar uScalar held.argument held.result
  have app : D B Γ (accepts (applicationGuard i L) (addressTerm sc (rawCons d e) gmin) u y) := by
    rw [exact_OriginalApplicationAcceptedGraph]
    exact rebuilt
  exact exact_OpenInheritedApplicationIntro data (applicationGuard i L) H c x u y
    (addressTerm sc (rawCons d e) gmin) step app

#print axioms renameStrictImageAligned
#print axioms exact_OpenStrictMeasuredInheritedImage
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredInheritedImageProof
