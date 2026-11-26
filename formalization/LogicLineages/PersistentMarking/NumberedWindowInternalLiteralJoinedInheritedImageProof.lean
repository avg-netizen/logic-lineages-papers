module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxImageTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationRebuildProof
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
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedInheritedImageProof
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
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
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
open NumberedWindowInternalLiteralBiAuxImageTransportProof (exact_OpenBiAuxCanonicalImage)
open NumberedWindowInternalLiteralStrictMeasuredCanonicalImageProof (exact_OpenStrictMeasuredReportedApplication)
open NumberedWindowInternalLiteralStrictImageAlignmentProof (StrictImageAligned)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalNeutralFactsTargets (direct inherited)
open NumberedWindowInternalLiteralInheritedApplicationProof (exact_OpenInheritedApplicationIntro exact_OriginalApplicationAcceptedGraph)
open NumberedWindowComputabilityFormulaTargets (accepts)

open NumberedWindowInternalLiteralBiAuxBaseWindowLiftProof (joinedBiAuxBase)
open NumberedWindowInternalLiteralBiAuxWindowLiftProof (exact_OpenJoinedWindowAssembly)
open NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof (joinedAuxiliaryWindow)
open NumberedWindowInternalLiteralStrictMeasuredCanonicalImageProof (exact_OpenLiteralAppAddressReport)
open NumberedWindowInternalLiteralApplicationRebuildProof (exact_OpenLiteralApplicationFromReportedLeast)

attribute [local irreducible] programGraph recursiveTypedMemo packedLeastOn direct
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The same original argument and the same certified result are used
to construct the inherited application on a genuine selected direct
function child. The argument movement is entirely class transport. -/
theorem exact_OpenJoinedInheritedImage (s : Settings) (X base : Program 2)
    (T V TV baseM cv tv : Program 1) (raw : Program 5) (finite : List Nat) (c : Nat)
    (x u y sc d e g a arg gmin after : OTerm α) :
    let C := measuredStrictCover V TV baseM
    let W := joinedAuxiliaryWindow s base T V TV baseM
    let Base := joinedBiAuxBase s X base T V TV baseM
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
  have image := exact_OpenBiAuxCanonicalImage s X T V TV baseM W
    (exact_OpenJoinedWindowAssembly s base T V TV baseM) sc d e g a gmin arg after
    reverse ends stable held.types fW aW least held.argLeast held.goalLeast
  have full := selected B α Γ sc e (auxiliaryTerm d e gmin arg) after image
  have rebuilt := exact_OpenLiteralApplicationFromReportedLeast i L
    (addressTerm sc (rawCons d e) gmin) u y sc d e gmin arg after
    (exact_OpenLiteralAppAddressReport sc (rawCons d e) gmin) held.argument fScalar uScalar full held.result
  have app : D B Γ (accepts (applicationGuard i L) (addressTerm sc (rawCons d e) gmin) u y) := by
    rw [exact_OriginalApplicationAcceptedGraph]
    exact rebuilt
  exact exact_OpenInheritedApplicationIntro data (applicationGuard i L) H c x u y
    (addressTerm sc (rawCons d e) gmin) step app

#print axioms exact_OpenJoinedInheritedImage
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedInheritedImageProof
