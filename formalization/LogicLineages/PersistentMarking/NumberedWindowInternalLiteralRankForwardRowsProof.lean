module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPushedForwardImageProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralForwardCoordinatesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredForwardPathProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalSelectedFormationAtGuardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteCodomainProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredSelectedGuardOrdinaryAddressProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationInputCoordinatesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPairedEdgeCoherenceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFormingCoherenceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredWindowOpenReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicAddressReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalScalarAddressWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalThinFormationRepresentativeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRankForwardRowsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (headTransport)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (refl symm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary rawCons)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalFreshProbeParsedEmitter (rawResult)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparsePositiveFold (positive)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalRankMeasuredExchange (rankedExchange)
open NumberedWindowInternalMeasuredExchangeThinDefinitions (measuredExchange)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (pairedExchange)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalMeasuredUnrestrictedSelectedFormationInputsProof (selectedWindow selectedBase)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (syntaxWindow coveredWindow)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntax)
open NumberedWindowInternalFactoredCoverTargets (factoredCover)
open NumberedWindowInternalCoverSelectedGrammarOptionTargets (selectedGrammarOption)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalAuxExchangeMemoTargets (selected)
open NumberedWindowInternalAuxExchangeMemoStepTargets (step)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalTransparentAuxRankTargets (auxRank)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalRankMeasuredForwardPathProof (exact_OpenOriginalRankMeasuredForwardPath)
open NumberedWindowInternalOriginalSelectedFormationAtGuardProof (exact_OpenOriginalSelectedGuardFormation)
open NumberedWindowInternalThinFormationRepresentativeSyntaxProof (atFunction)
open NumberedWindowInternalSparseCoveredWindowOpenReportProof (exact_CoveredWindowReport)
open NumberedWindowInternalPullbackTargets (forwardImage)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalLiteralPositiveEndpointGuardProof (positiveEndpointGuard)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (D finiteCodes finiteScalar exact_OpenLiteralFiniteScalar)
open NumberedWindowInternalLiteralTypeMembershipTargets (literalMembership)
open NumberedWindowInternalLiteralFiniteCodomainProof (exact_OpenLiteralFiniteCodomain)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ChildClosed)
open NumberedWindowInternalLiteralAtomicAddressReportProof (alignSource)
open NumberedWindowInternalLiteralApplicationInputCoordinatesProof (exact_OpenLiteralApplicationInputCoordinates)
open NumberedWindowInternalOriginalScalarAddressWindowProof (exact_OpenOriginalScalarAddressWindow)
open NumberedWindowInternalLiteralPairedEdgeCoherenceProof (exact_OriginalPairedSelectedMinimum)
open NumberedWindowInternalLiteralFormingCoherenceProof (exact_OpenCoherenceFromWindowDomain)
open NumberedWindowInternalLiteralForwardCoordinatesProof
open NumberedWindowInternalLiteralPushedForwardImageProof
open NumberedWindowInternalOriginalFirstHopCoreProof (literalAddress)

attribute [local irreducible] programGraph
variable {α : Type} {Γ : List (Formula α)}

def OpenRankTypeGuards (P : List ProbeTy) (TG TV : Program 1) : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (t : OTerm α),
    D B Γ (literalMembership (finiteCodes P) t) →
    D B Γ (unary TG (suc z) t) ∧ D B Γ (unary TV (suc z) t)

theorem exact_OpenRankCoveredCoherence (C baseW : Program 3) (D₀ : Program 2) (s : Settings) :
    NumberedWindowInternalLiteralRoundLeastTargets.SameLeastOnEdge
      C (guardedExchange C s (pairedExchange D₀)) (coveredWindow C s baseW) s := by
  let X := guardedExchange C s (pairedExchange D₀)
  let W := coveredWindow C s baseW
  apply exact_OpenCoherenceFromWindowDomain C X W s (exact_OriginalPairedSelectedMinimum C D₀ W s)
  intro B α Γ ctx ty seed pass
  obtain ⟨w⟩ := pass
  obtain ⟨rule⟩ := exact_CoveredWindowReport C X s baseW B α Γ ctx ty seed
  have h := Derivation.implicationElimination rule w
  exact ⟨Derivation.conjunctionRight (Derivation.conjunctionRight h)⟩

/-- Both original open interfaces are aligned: the accepted application's
typed function address is the positive certificate's source, and its
later function is the original target address. The rank-measured
physical matching theorem is used without any program substitution. -/
theorem exact_OpenRankForwardFromRows (s : Settings) (P : List ProbeTy) (closed : ChildClosed P)
    (base intrinsic : Program 2) (V TV T baseM cv tv rank : Program 1) (root other : Program 3)
    (c : Nat) (f g u x ctx res dom cod fn arg before sc st fromTerm dest path : OTerm α) :
    let Tg := conjunction (refitGuard s T) TV
    let Va := auxSyntax V TV
    let M := selectedMeasure (measureUpdate baseM chosenCombine)
    let C := factoredCover Va M selectedGrammarOption
    let W := selectedWindow s intrinsic Tg V TV baseM
    let D₀ := measuredExchange (auxRank rank) (measuredExchange M (selected (step base Va)))
    let X := guardedExchange C s (pairedExchange D₀)
    let raw := typedRaw5 root other W Va
    let L := packedLeastProgram C X W s
    let i := finiteScalar (addressScalar cv tv W L) (finiteCodes P)
    let data := literalData i (positiveEndpointGuard i (addressPositive cv tv raw L))
    let B := sourceBody data c
    OpenRankTypeGuards P Tg tv →
    D B Γ (unary i (suc z) f) → D B Γ (unary i (suc z) g) → D B Γ (unary i (suc z) u) →
    D B Γ (parsedApplicationInputs f u ctx res dom cod fn arg) →
    D B Γ (leastGraph C X W s ctx cod (auxiliaryTerm dom cod fn arg) before) →
    D B Γ (eqn x (addressTerm ctx cod before)) →
    D B Γ (addressReport f sc st fromTerm) → D B Γ (addressReport g sc st dest) →
    D B Γ (programGraph (positive raw L) (suc z) ![sc,st,fromTerm,path,dest]) →
    D B Γ (forwardImage data (applicationGuard i L) c g u x) := by
  intro Tg Va M C W D₀ X raw L i data B typeRule hf hg hu parsed original emitted start finish step
  let funTy := rawCons dom cod
  let baseScalar := addressScalar cv tv W L
  obtain ⟨fnReport,argReport,feq⟩ := exact_OpenParsedOperandAddresses f u ctx res dom cod fn arg parsed
  obtain ⟨ec,et,eqf⟩ := alignSource f ctx funTy fn sc st fromTerm feq start
  have gReport := exact_OpenRetapeAddress g sc st dest ctx funTy dest finish ec et ⟨refl dest⟩
  have pathHeld := exact_OpenRetapePositiveFold (positive raw L) sc st fromTerm path dest ctx funTy fn ec et eqf step
  obtain ⟨fr⟩ := fnReport
  obtain ⟨gr⟩ := gReport
  obtain ⟨ar⟩ := argReport
  have fTy : D B Γ (unary rawResult funTy f) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight fr))⟩
  have gTy : D B Γ (unary rawResult funTy g) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight gr))⟩
  have aTy : D B Γ (unary rawResult dom u) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight ar))⟩
  obtain ⟨scalarF,typesF⟩ := exact_OpenLiteralFiniteScalar baseScalar (finiteCodes P) f funTy fTy hf
  obtain ⟨scalarG,_⟩ := exact_OpenLiteralFiniteScalar baseScalar (finiteCodes P) g funTy gTy hg
  obtain ⟨scalarU,typesU⟩ := exact_OpenLiteralFiniteScalar baseScalar (finiteCodes P) u dom aTy hu
  have typesCod := exact_OpenLiteralFiniteCodomain P closed dom cod typesF
  obtain ⟨domT,_⟩ := typeRule B α Γ dom typesU
  obtain ⟨codT,codTV⟩ := typeRule B α Γ cod typesCod
  obtain ⟨domT⟩ := domT
  obtain ⟨codT⟩ := codT
  have two : D B Γ (unary Tg (suc z) dom ⊓ unary Tg (suc z) cod) :=
    ⟨Derivation.conjunctionIntroduction domT codT⟩
  obtain ⟨gc,_,_,winF,winU⟩ := exact_OpenLiteralApplicationInputCoordinates cv tv W L
    f u ctx res dom cod fn arg scalarF scalarU parsed
  obtain ⟨gRaw⟩ := exact_OpenOriginalScalarAddressWindow cv tv W L g ctx funTy dest ⟨gr⟩ scalarG
  let winG := Derivation.conjunctionLeft gRaw
  have form := exact_OpenOriginalSelectedGuardFormation s intrinsic T V TV baseM ctx dom cod arg two winU
  obtain ⟨formD⟩ := form
  obtain ⟨prev⟩ := atFunction W ctx dom cod arg fn formD
  obtain ⟨next⟩ := atFunction W ctx dom cod arg dest formD
  obtain ⟨winF⟩ := winF
  have earlierWin := Derivation.implicationElimination prev winF
  have laterWin := Derivation.implicationElimination next winG
  have paid := exact_OpenRankCoveredCoherence C (syntaxWindow (selectedBase intrinsic Tg) Va) D₀ s
  have xs := exact_OpenPlainFiniteScalarAtLeast cv tv C W X s paid (finiteCodes P)
    ctx cod (auxiliaryTerm dom cod fn arg) before gc codTV typesCod ⟨earlierWin⟩ original
  obtain ⟨eqX⟩ := emitted
  have actualX := headTransport i (suc z) (literalAddress ctx cod before) x ![] ⟨symm eqX⟩ xs
  have atX := exact_OpenLiteralReportedAddress x ctx cod before ⟨eqX⟩
  have push := exact_OpenOriginalRankMeasuredForwardPath s base Va baseM rank chosenCombine
    selectedGrammarOption (selectedBase intrinsic Tg) root other B α Γ ctx dom cod arg fn dest path before
    ⟨formD⟩ ⟨winG⟩ pathHeld original
  exact exact_OpenForwardImageFromPushed cv tv C W X s raw paid (finiteCodes P)
    c g u x ctx dom cod dest arg before gc codTV typesCod ⟨laterWin⟩ ⟨gr⟩ hg ⟨ar⟩ hu atX actualX push

#print axioms exact_OpenRankCoveredCoherence
#print axioms exact_OpenRankForwardFromRows
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRankForwardRowsProof
