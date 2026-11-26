module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictDualAllApplicationRowsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSealedWindowProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedInheritedImageProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredInheritedImageProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedMemoPacketProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralWindowMemoChildFromForkProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedAllApplicationCasesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ChildClosed)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof (CanReverse)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (finiteCodes finiteScalar)
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn)
open NumberedWindowInternalLiteralLeastOnFixedPointProof (WindowEndpoints)
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictCover)
open NumberedWindowInternalLiteralStrictMeasuredPlainLiftProof
open NumberedWindowInternalLiteralStrictMeasuredEnrichedLiftProof
open NumberedWindowInternalLiteralStrictMeasuredMemoTransportProof (selectedBiAuxType)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)
open NumberedWindowInternalLiteralTypedMemoUnfoldingProof (recursiveTypedMemo)
open NumberedWindowInternalLiteralTypedMemoLeastLawsProof (memoFilteredLeast MemoSelectedReports)
open NumberedWindowInternalLiteralStrictImageAlignmentProof
open NumberedWindowInternalLiteralStrictMeasuredInheritedImageProof
open NumberedWindowInternalLiteralInheritedApplicationProof (exact_InheritedApplicationRename exact_OriginalApplicationAcceptedGraph)
open NumberedWindowInternalLiteralRankForwardRowsProof (OpenRankTypeGuards)
open NumberedWindowInternalLiteralStrictDualAllApplicationRowsProof (exact_OpenStrictDualAllApplicationRows)
open NumberedWindowInternalLiteralWindowMemoChildFromForkProof (exact_OpenWindowMemoChildFromFork)
open NumberedWindowInternalLiteralStrictDualChildProof (strictDualRaw)
open NumberedWindowInternalLiteralAtomicRawGuardProof (guardedRaw)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalNeutralFactsTargets (atom direct inherited)
open NumberedWindowInternalLiteralNeutralAtomProof (neutralSource)
open NumberedWindowInternalAtomicRefinement (bottomSource)
open NumberedWindowComputabilityFormulaTargets (accepts)

open NumberedWindowInternalLiteralJoinedInheritedImageProof (exact_OpenJoinedInheritedImage)
open NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof
open NumberedWindowInternalLiteralBiAuxBaseWindowLiftProof (joinedBiAuxBase)
open NumberedWindowInternalLiteralJoinedRawFunctionLiftProof (selectedJoinedRaw exact_OpenSelectedJoinedRawWindows)
open NumberedWindowInternalLiteralStrictMeasuredPlainLiftProof (selectedBiAuxWindow)
open NumberedWindowInternalLiteralCoveredMemoAuxRowProof (childAtWindow)
open NumberedWindowInternalLiteralSealedWindowProof (exact_OpenSealedWindow)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)

open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open NumberedWindowInternalSparsePathSuccessfulAdvanceTargets (hopCalls)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs)
open NumberedWindowInternalLiteralRootDispatchOpenProof (bit)
open NumberedWindowInternalLiteralAuxRootLeaf (functionLambdaHeader)
open NumberedWindowInternalSparseRawRunRootTargets (rootWitnessTerm)

attribute [local irreducible] programGraph recursiveTypedMemo packedLeastOn direct
variable {α : Type} {Γ : List (Formula α)}

/-- The actual application result's direct step is bottom, or an exact
inherited application, or the original successful beta leaf. This is
the unconditional case split at the checked application, with all
non-beta work discharged on the same joined tuple. -/
theorem exact_OpenJoinedAllApplicationCases
    (s : Settings) (P : List ProbeTy) (closed : ChildClosed P) (X base : Program 2)
    (T V baseM cv tv : Program 1) (leaf : Nat → Program 3) (other : Program 3)
    (c : Nat) (x u t y : OTerm α) (betaGoal : Formula α) :
    let Tg := selectedBiAuxType s T tv
    let Va := unitAuxSyntax V tv
    let C := measuredStrictCover V tv baseM
    let W := joinedAuxiliaryWindow s base Tg V tv baseM
    let Base := joinedBiAuxBase s X base Tg V tv baseM
    let E := recursiveTypedMemo Base
    let L₀ := packedLeastOn C E s
    let L := memoFilteredLeast C Base s
    let i := finiteScalar (addressScalar cv tv W L) (finiteCodes P)
    let raw := guardedRaw (strictDualRaw C s leaf other base base Tg Va Tg)
    let R := rawWithTarget i cv tv raw L
    let data := S i cv tv R L
    let H := hop cv tv R L
    let B := sourceBody data c
    CanReverse Base → WindowEndpoints W E → Preserves E L₀ → MemoSelectedReports C s Base →
    OpenRankTypeGuards P Tg tv →
    D B Γ (accepts (applicationGuard i L) x u t) →
    D B Γ (direct data H c t y) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (ctx result dom cod fn arg k sc st before after cert q w r payload : OTerm β),
      (∀ φ ∈ Γ, φ.relabel j ∈ Δ) →
      D B Δ (unary i (suc z) (x.relabel j)) → D B Δ (unary i (suc z) (u.relabel j)) →
      D B Δ (parsedApplicationInputs (x.relabel j) (u.relabel j) ctx result dom cod fn arg) →
      D B Δ (addressReport (y.relabel j) sc st after) →
      D B Δ (eqn sc ctx) → D B Δ (eqn st cod) → D B Δ (eqn before k) →
      D B Δ (programGraph L (suc before) ![sc,st,auxiliaryTerm dom cod fn arg]) →
      D B Δ (eqn w (rootWitnessTerm payload)) → D B Δ (bit (leaf 6) ![q,payload,r]) →
      D B Δ (bit functionLambdaHeader ![q,payload,r]) →
      D B Δ (hopCalls R L sc st before cert after q w r) → D B Δ (betaGoal.relabel j)) →
    D B Γ (atom bottomSource y ⊔ (inherited data (applicationGuard i L) H c x u y ⊔ betaGoal)) := by
  intro Tg Va C W Base E L₀ L i raw R data H B reverse ends stable selected types accepted hopNow beta
  let earlier := inherited data (applicationGuard i L) H c x u y
  let goal := earlier ⊔ betaGoal
  have app : D B Γ (programGraph (applicationGuard i L) (suc z) ![x,u,t]) := by
    rw [← exact_OriginalApplicationAcceptedGraph]
    exact accepted
  apply exact_OpenStrictDualAllApplicationRows C (selectedBiAuxExchange s X V tv baseM) s
    leaf other base base Tg Va Tg i cv tv L₀ c x u t y goal app hopNow
  · intro β j Δ ctx result dom cod fn arg k sc st before after cert q w r payload
      keep left right parsed address scope outputType eqBefore parent witness rule head calls
    have yes := beta β j Δ ctx result dom cod fn arg k sc st before after cert q w r payload
      keep left right parsed address scope outputType eqBefore parent witness rule head calls
    obtain ⟨yes⟩ := yes
    exact ⟨orRight yes⟩
  · intro β j Δ ctx result dom cod fn arg k sc st before after cert q w r d e f a child d' e' g a'
      keep left right parsed address scope outputType _ parent parts rawFacts windows calls
    obtain ⟨rawFacts⟩ := rawFacts
    obtain ⟨windows⟩ := windows
    obtain ⟨physical⟩ := calls
    let hopFacts := Derivation.conjunctionRight (Derivation.conjunctionRight physical)
    have aligned := exact_OpenStrictImageAlignment s P closed cv tv T W L₀
      (x.relabel j) (u.relabel j) (y.relabel j) ctx result dom cod fn arg sc st before after q r d e f a d' e' g a'
      types left right parsed address scope outputType parent ⟨Derivation.conjunctionLeft hopFacts⟩
      ⟨Derivation.conjunctionRight hopFacts⟩ parts.source parts.target parts.domEq parts.codEq parts.argEq
    have rawChild : D B Δ (programGraph (selectedJoinedRaw s base Tg V tv baseM leaf other)
        (suc z) ![sc,rawCons d e,f,child,g]) := ⟨Derivation.conjunctionLeft rawFacts⟩
    have fWindow := (exact_OpenSelectedJoinedRawWindows s base Tg V tv baseM leaf other
      sc (rawCons d e) f child g rawChild).2
    have strictF : D B Δ (windowAt (selectedBiAuxWindow s base Tg V tv baseM) sc (rawCons d e) g) :=
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight windows)⟩
    have cover := ((exact_OpenSealedWindow C s (strictAuxWindow base Tg) sc (rawCons d e) g).1 strictF).2
    have strictA : D B Δ (windowAt (selectedBiAuxWindow s base Tg V tv baseM) sc d a) :=
      ⟨Derivation.conjunctionRight (Derivation.conjunctionRight windows)⟩
    have aWindow := (exact_OpenJoinedAuxiliaryWindow s base Tg V tv baseM sc d a).mpr
      ⟨strictA,⟨Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionRight rawFacts))⟩⟩
    have nonBeta : D B Δ (earlier.relabel j) := by
      rw [exact_InheritedApplicationRename]
      apply exact_OpenWindowMemoChildFromFork cv tv C Base s W raw (finiteCodes P) c
        (x.relabel j) (u.relabel j) ctx result dom cod fn arg sc st before after cert q w r d e f a child g
        (inherited data (applicationGuard i L) H c (x.relabel j) (u.relabel j) (y.relabel j))
        ends stable selected left right parsed scope parent parts.source ⟨Derivation.conjunctionLeft rawFacts⟩
        fWindow cover ⟨physical⟩
      intro γ n Θ m stay least childScalar generated
      rw [exact_InheritedApplicationRename]
      have fixed := renameStrictImageAligned s Tg tv L₀ sc d e g a arg (u.relabel j) (y.relabel j)
        after n stay aligned
      have fw := renameInto fWindow n Θ stay
      rw [windowRename,rawConsRename] at fw
      have aw := renameInto aWindow n Θ stay
      rw [windowRename] at aw
      have us := renameInto right n Θ stay
      rw [unaryRename,sucRelabel,zRelabel] at us
      exact exact_OpenJoinedInheritedImage s X base Tg V tv baseM cv tv raw (finiteCodes P) c
        ((x.relabel j).relabel n) ((u.relabel j).relabel n) ((y.relabel j).relabel n)
        (sc.relabel n) (d.relabel n) (e.relabel n) (g.relabel n) (a.relabel n) (arg.relabel n) m (after.relabel n)
        reverse ends stable selected fixed fw aw least childScalar us generated
    obtain ⟨nonBeta⟩ := nonBeta
    exact ⟨orLeft nonBeta⟩

#print axioms exact_OpenJoinedAllApplicationCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedAllApplicationCasesProof
