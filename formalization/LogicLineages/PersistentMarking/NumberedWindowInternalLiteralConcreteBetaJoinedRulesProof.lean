module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaJoinedMemoPacketProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaApplicationComputabilityProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedComputabilityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFreshNeutralBridgeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedMemoInversionProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedForwardRuleProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralConcreteStrictMeasuredInversionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackChecks
import LogicLineages.PersistentMarking.NumberedWindowGuardedGraphChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralAtomProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralResidualProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralInheritedApplicationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralConcreteBetaJoinedRulesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (Data sourceBody)
open ID1Completion.InternalControlGraph (programGraph)
open ID1Completion.InternalAccessibilityRules (carrier)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalNeutralFactsTargets (Arithmetic FactsAt atom direct inherited)
open NumberedWindowInternalLiteralNeutralAtomProof (neutralSource exact_LiteralNeutralFromApplications)
open NumberedWindowInternalAtomicRefinement (bottomSource freeSource)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)
open NumberedWindowInternalLiteralCoveredMemo (WindowSeedsCovered)
open NumberedWindowInternalSettingsGrammarGuardNumericTargets (GrammarTypeInclusion)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (finiteCodes finiteScalar)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard applicationCore)
open NumberedWindowInternalLiteralDirectCarrierInstalledProof (Packet)
open NumberedWindowInternalLiteralAtomicRawGuardProof (guardedRaw)
open NumberedWindowInternalLiteralStrictDualChildProof (strictDualRaw)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalLiteralBetaJoinedMemoPacketProof (exact_ConcreteBetaJoinedMemoPacket)
open NumberedWindowInternalLiteralJoinedMemoInversionProof (exact_OpenJoinedMemoInversion)
open NumberedWindowInternalLiteralStrictMeasuredMemoTransportProof (selectedBiAuxType)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictCover)
open NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof (joinedAuxiliaryWindow)
open NumberedWindowInternalLiteralBiAuxBaseWindowLiftProof (joinedBiAuxBase)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)
open NumberedWindowInternalLiteralTypedMemoLeastLawsProof (memoFilteredLeast)
open NumberedWindowInternalLiteralNeutralResidualProof (exact_LiteralArithmeticFromResidual)
open NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof (fullAuxiliaryDecorator)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralTypedMemoUnfoldingProof (recursiveTypedMemo)
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn)
open NumberedWindowInternalLiteralInheritedApplicationProof (exact_OriginalApplicationAcceptedGraph)

open NumberedWindowInternalLiteralConcreteStrictMeasuredInversionProof (InstalledNeutralInversion)
open NumberedWindowInternalLiteralJoinedForwardRuleProof (exact_OpenJoinedForwardRule)
open NumberedWindowInternalPullbackTargets (ForwardRule Pullback)
open NumberedWindowInternalPullbackChecks (exact_InternalPullback)
open NumberedWindowGuardedGraphChecks (exact_GuardRules)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)

open LogicLineages.OrdinalComparison.Source (Ty)
open ID1Completion.InternalAccessibilityRules (membership)
open NumberedWindowInternalLiteralBetaLeafProof (InstanceFit withBetaLeaf)
open NumberedWindowInternalLiteralJoinedBetaOutcomeProof (exact_OpenJoinedBetaOutcome)
open NumberedWindowInternalLiteralBetaApplicationComputabilityProof (BetaApplicationCases ApplicationOutput)
open NumberedWindowInternalLiteralFreshNeutralBridgeProof
  (exact_LiteralFreshFromNeutral exact_TupleComputabilityToIFromArithmetic)
open NumberedWindowInternalFreshProbeParsedTyped (chosenH chosenA)
open NumberedWindowInternalProbeTargets (FreshVariablesComputable typedAt)
open NumberedWindowInternalNeutralFactsProof (exact_ConditionalInternalNeutralFacts)
open NumberedWindowComputabilityFormulaTargets (formula)

structure BetaJoinedRulesAt (data : Data) (i : Program 1) (p h L₀ L : Program 3) (U : Program 2)
    (P : List ProbeTy) (v : Inputs) (c : Nat) : Prop where
  inversion : InstalledNeutralInversion data p h c
  arithmetic : Arithmetic data p h neutralSource bottomSource freeSource c
  forward : ForwardRule data p c
  pullback : Pullback data p c
  applicationOutput : ApplicationOutput data p neutralSource c
  betaCases : BetaApplicationCases data p h L₀ L i bottomSource U c
  fresh : FreshVariablesComputable data v.applicationGuard (chosenH v P) (chosenA v) c
  typedComputableToMember : ∀ (τ : Ty) (α : Type) (Γ : List (Formula α)) (q : OTerm α),
    NumberedWindowInternalNeutralFactsTargets.D data c Γ (typedAt (chosenH v P) τ q) →
    NumberedWindowInternalNeutralFactsTargets.D data c Γ (formula v.applicationGuard τ q) →
    NumberedWindowInternalNeutralFactsTargets.D data c Γ (membership false q)

/-- Choose one original all-input-calibrated checker carrying the
actual beta instance call, neutral inversion, positive forward and
pullback, and typed computability-to-I. Beta cases identify the real
instance and exact selected destination; a proof of computability
of that instance is not asserted for arbitrary abstractions. -/
theorem exact_ConcreteBetaJoinedRules (xs : Entries) (s : Settings) (P : List ProbeTy)
    (valid : ValidWindow s P) (seeds : WindowSeedsCovered s) (symmetric : HeadPairsSymmetric s.equivalentHeads)
    (grammar : GrammarTypeInclusion s) (included : ∀ t ∈ finiteCodes P, t ∈ s.window.1) :
    ∃ (i cv tv : Program 1) (U : Program 2) (raw : Program 5) (L₀ L : Program 3) (placed : Inputs),
      InstanceFit U ∧ Packet xs s P i cv tv raw L (applicationCore L) placed ∧
      placed.applicationGuard = applicationGuard i L ∧
      (∀ c : Nat, let R := rawWithTarget i cv tv raw L
        let data := S i cv tv R L
        BetaJoinedRulesAt data i (applicationGuard i L) (hop cv tv R L) L₀ L U P placed c) := by
  obtain ⟨cv,tv,U,leaves,other,X,base,T,V,baseM,placed,fit,packet,placedApp,reverse,ends,stable,selected,guards,closed⟩ :=
    exact_ConcreteBetaJoinedMemoPacket xs s P valid seeds symmetric grammar included
  let Tg := selectedBiAuxType s T tv
  let C := measuredStrictCover V tv baseM
  let W := joinedAuxiliaryWindow s base Tg V tv baseM
  let Base := joinedBiAuxBase s X base Tg V tv baseM
  let L₀ := packedLeastOn C (recursiveTypedMemo Base) s
  let L := memoFilteredLeast C Base s
  let i := finiteScalar (addressScalar cv tv W L) (finiteCodes P)
  let Va := unitAuxSyntax V tv
  let leaf := withBetaLeaf Va U leaves
  let raw := guardedRaw (strictDualRaw C s leaf other base base Tg Va Tg)
  refine ⟨i,cv,tv,U,raw,L₀,L,placed,fit,packet,placedApp,?_⟩
  intro c R data
  have f := exact_OpenJoinedForwardRule s P valid.2.1 X base T V baseM cv tv leaf other c
    reverse ends stable selected guards
  let r := addressPositive cv tv R L
  let d := dCore i r permutation
  have guardsP := (exact_GuardRules i (jRaw i) r d (applicationCore L)).1
  have back : Pullback data (applicationGuard i L) c :=
    exact_InternalPullback i (jRaw i) r d (applicationGuard i L) c guardsP f
  have inversion : InstalledNeutralInversion data (applicationGuard i L) (hop cv tv R L) c := by
    intro α Γ x u t y neutral app step
    exact exact_OpenJoinedMemoInversion s P valid.2.1 X base T V baseM cv tv leaf other c x u t y
      reverse ends stable selected guards neutral app step
  have rem := exact_LiteralNeutralFromApplications i cv tv (strictDualRaw C s leaf other base base Tg Va Tg)
    (headerLeast (fullAuxiliaryDecorator (packedLeastOn C (recursiveTypedMemo Base) s))) (applicationGuard i L) c
    ⟨(fun α Γ x u y _ app => by
      rw [exact_OriginalApplicationAcceptedGraph] at app
      exact closed c α Γ x u y app), inversion⟩
  have arithmetic := exact_LiteralArithmeticFromResidual i cv tv raw L (applicationGuard i L)
    neutralSource bottomSource c packet.directRules rem
  have allCases : BetaApplicationCases data (applicationGuard i L) (hop cv tv R L) L₀ L i bottomSource U c := by
    intro α Γ x u t y goal app step beta
    exact exact_OpenJoinedBetaOutcome s P valid.2.1 X base U T V baseM cv tv leaves other
      c x u t y goal reverse ends stable selected guards app step beta
  have arithAt : Arithmetic data placed.applicationGuard (hop cv tv R L) neutralSource bottomSource freeSource c := by
    rw [placedApp]
    exact arithmetic
  have forwardAt : ForwardRule data placed.applicationGuard c := by
    rw [placedApp]
    exact f
  have tuple := packet.physical.1
  obtain ⟨_,_,_,_,_,_,_,_,_,shape,aligned⟩ := tuple
  have fresh := exact_LiteralFreshFromNeutral placed P data (hop cv tv R L) neutralSource bottomSource c shape (aligned c) arithAt
  refine ⟨inversion,arithmetic,f,back,?_,allCases,fresh,?_⟩
  · intro α Γ x u t accepted
    rw [exact_OriginalApplicationAcceptedGraph] at accepted
    exact closed c α Γ x u t accepted
  · intro τ α Γ q typed computed
    exact exact_TupleComputabilityToIFromArithmetic xs s P i (jRaw i) r d placed c
      (hop cv tv R L) neutralSource bottomSource packet.physical.1 arithAt forwardAt τ α Γ q typed computed

#print axioms BetaJoinedRulesAt
#print axioms exact_ConcreteBetaJoinedRules
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralConcreteBetaJoinedRulesProof
