module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedMemoInversionProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedForwardRuleProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralConcreteStrictMeasuredInversionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackChecks
import LogicLineages.PersistentMarking.NumberedWindowGuardedGraphChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralAtomProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralResidualProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralInheritedApplicationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralConcreteJoinedApplicationRulesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (Data sourceBody)
open ID1Completion.InternalControlGraph (programGraph)
open ID1Completion.InternalAccessibilityRules (carrier)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalNeutralFactsTargets (Arithmetic atom direct inherited)
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
open NumberedWindowInternalLiteralJoinedMemoPacketProof (exact_ConcreteJoinedMemoPacket)
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

/-- One physical instance supplies the original numeric checker, the
direct rules, both original application closure clauses, full neutral
inversion, and forward transport and pullback on the untouched
positive relation of that very same checker. -/
theorem exact_ConcreteJoinedApplicationRules (xs : Entries) (s : Settings) (P : List ProbeTy)
    (valid : ValidWindow s P) (seeds : WindowSeedsCovered s) (symmetric : HeadPairsSymmetric s.equivalentHeads)
    (grammar : GrammarTypeInclusion s) (included : ∀ t ∈ finiteCodes P, t ∈ s.window.1) :
    ∃ (i cv tv : Program 1) (raw : Program 5) (L : Program 3) (placed : Inputs),
      Packet xs s P i cv tv raw L (applicationCore L) placed ∧
      placed.applicationGuard = applicationGuard i L ∧
      (∀ c : Nat, let R := rawWithTarget i cv tv raw L
        let data := S i cv tv R L
        InstalledNeutralInversion data (applicationGuard i L) (hop cv tv R L) c ∧
        Arithmetic data (applicationGuard i L) (hop cv tv R L) neutralSource bottomSource freeSource c ∧
        ForwardRule data (applicationGuard i L) c ∧ Pullback data (applicationGuard i L) c ∧
        (∀ (α : Type) (Γ : List (Formula α)) (f u y : OTerm α),
          D (sourceBody data c) Γ (programGraph (applicationGuard i L) (suc z) ![f,u,y]) →
          D (sourceBody data c) Γ (carrier data false c y) ∧ D (sourceBody data c) Γ (atom neutralSource y))) := by
  obtain ⟨cv,tv,leaf,other,X,base,T,V,baseM,placed,packet,placedApp,reverse,ends,stable,selected,guards,closed⟩ :=
    exact_ConcreteJoinedMemoPacket xs s P valid seeds symmetric grammar included
  let Tg := selectedBiAuxType s T tv
  let C := measuredStrictCover V tv baseM
  let W := joinedAuxiliaryWindow s base Tg V tv baseM
  let Base := joinedBiAuxBase s X base Tg V tv baseM
  let L := memoFilteredLeast C Base s
  let i := finiteScalar (addressScalar cv tv W L) (finiteCodes P)
  let Va := unitAuxSyntax V tv
  let raw := guardedRaw (strictDualRaw C s leaf other base base Tg Va Tg)
  refine ⟨i,cv,tv,raw,L,placed,packet,placedApp,?_⟩
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
  exact ⟨inversion,arithmetic,f,back,closed c⟩

#print axioms exact_ConcreteJoinedApplicationRules
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralConcreteJoinedApplicationRulesProof
