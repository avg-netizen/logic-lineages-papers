module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredMemoInversionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralConcreteStrictMeasuredInversionProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (Data sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalNeutralFactsTargets (atom direct inherited)
open NumberedWindowInternalLiteralNeutralAtomProof (neutralSource)
open NumberedWindowInternalAtomicRefinement (bottomSource)
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
open NumberedWindowInternalLiteralStrictMeasuredMemoPacketProof (exact_ConcreteStrictMeasuredMemoPacket)
open NumberedWindowInternalLiteralStrictMeasuredMemoInversionProof (exact_OpenStrictMeasuredMemoInversion)
open NumberedWindowInternalLiteralStrictMeasuredMemoTransportProof (selectedBiAuxType)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictCover)
open NumberedWindowInternalLiteralStrictMeasuredPlainLiftProof (selectedBiAuxWindow)
open NumberedWindowInternalLiteralStrictMeasuredEnrichedLiftProof (selectedBiAuxBase)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)
open NumberedWindowInternalLiteralTypedMemoLeastLawsProof (memoFilteredLeast)

/-- The original open neutral inversion clause on the supplied actual
programs, including the exact bottom-or-inherited conclusion. -/
def InstalledNeutralInversion (data : Data) (app h : Program 3) (c : Nat) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (x u t y : OTerm α),
    D (sourceBody data c) Γ (atom neutralSource x) →
    D (sourceBody data c) Γ (accepts app x u t) →
    D (sourceBody data c) Γ (direct data h c t y) →
    D (sourceBody data c) Γ (atom bottomSource y ⊔ inherited data app h c x u y)

/-- The concrete original numerical packet and the full neutral
inversion hold on one and the same installed tuple. The formula of
inversion is exactly the manuscript's bottom or inherited application. -/
theorem exact_ConcreteStrictMeasuredMemoInversion (xs : Entries) (s : Settings) (P : List ProbeTy)
    (valid : ValidWindow s P) (seeds : WindowSeedsCovered s) (symmetric : HeadPairsSymmetric s.equivalentHeads)
    (grammar : GrammarTypeInclusion s) (included : ∀ t ∈ finiteCodes P, t ∈ s.window.1) :
    ∃ (i cv tv : Program 1) (raw : Program 5) (L : Program 3) (placed : Inputs),
      Packet xs s P i cv tv raw L (applicationCore L) placed ∧
      (∀ c : Nat, let R := rawWithTarget i cv tv raw L
        InstalledNeutralInversion (S i cv tv R L) (applicationGuard i L) (hop cv tv R L) c) := by
  obtain ⟨cv,tv,leaf,other,X,base,T,V,baseM,placed,packet,reverse,ends,stable,selected,guards,_⟩ :=
    exact_ConcreteStrictMeasuredMemoPacket xs s P valid seeds symmetric grammar included
  let Tg := selectedBiAuxType s T tv
  let C := measuredStrictCover V tv baseM
  let W := selectedBiAuxWindow s base Tg V tv baseM
  let Base := selectedBiAuxBase s X base Tg V tv baseM
  let L := memoFilteredLeast C Base s
  let i := finiteScalar (addressScalar cv tv W L) (finiteCodes P)
  let Va := unitAuxSyntax V tv
  let raw := guardedRaw (strictDualRaw C s leaf other base base Tg Va Tg)
  refine ⟨i,cv,tv,raw,L,placed,packet,?_⟩
  intro c R
  unfold InstalledNeutralInversion
  intro α Γ x u t y neutral app step
  exact exact_OpenStrictMeasuredMemoInversion s P valid.2.1 X base T V baseM cv tv leaf other c x u t y
    reverse ends stable selected guards neutral app step

#print axioms exact_ConcreteStrictMeasuredMemoInversion
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralConcreteStrictMeasuredInversionProof
