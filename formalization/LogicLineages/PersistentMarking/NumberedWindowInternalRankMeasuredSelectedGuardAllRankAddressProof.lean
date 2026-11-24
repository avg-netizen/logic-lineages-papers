module
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredForwardPathProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalSelectedFormationAtGuardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalScalarAddressWindowProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalAddressAtKnownFoldProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankPartitionedAddressOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalRankCheckedLeastDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredMatchedPathProof
import LogicLineages.PersistentMarking.NumberedWindowInternalRankPartitionAllFoldProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredSelectedGuardAllRankAddressProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z rawCons)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparsePositiveFold (positive)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntax)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalFactoredCoverTargets (factoredCover)
open NumberedWindowInternalCoverSelectedGrammarOptionTargets (selectedGrammarOption)
open NumberedWindowInternalRankMeasuredExchange (rankedExchange)
open NumberedWindowInternalMeasuredExchangeThinDefinitions (measuredExchange)
open NumberedWindowInternalAuxExchangeMemoStepTargets (step)
open NumberedWindowInternalAuxExchangeMemoTargets (selected)
open NumberedWindowInternalTransparentAuxRankTargets (auxRank)
open NumberedWindowInternalRankPartitionedAddress (rankPartitionedAddress)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalMeasuredUnrestrictedSelectedFormationInputsProof (selectedWindow selectedBase)
open NumberedWindowInternalThinMatchedForwardBindingProof (pushed)
open NumberedWindowInternalRankMeasuredForwardPathProof (exact_OpenOriginalRankMeasuredForwardPath)
open NumberedWindowInternalOriginalSelectedFormationAtGuardProof (exact_OpenOriginalSelectedGuardFormation)
open NumberedWindowInternalOriginalScalarAddressWindowProof
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalThinMatchedCallsTargets (pulled)
open NumberedWindowInternalRankMeasuredMatchedPathProof (exact_OriginalRankMeasuredMatchedPath)
open NumberedWindowInternalRankPartitionAllFoldProof (exact_OpenRankPartitionOrdinaryFold)

theorem exact_OpenOriginalAllRankSelectedGuardAddressForward
    (s : Settings) (base intrinsic : Program 2) (V TV T baseM cv tv g : Program 1) (root other : Program 3)
    (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (x y ctx dom cod arg f n cert value : OTerm α) :
    let Tg := conjunction (refitGuard s T) TV
    let Va := auxSyntax V TV
    let M := selectedMeasure (measureUpdate baseM chosenCombine)
    let C := factoredCover Va M selectedGrammarOption
    let W := selectedWindow s intrinsic Tg V TV baseM
    let H := auxRank g
    let D := measuredExchange M (selected (step base Va))
    let X := rankedExchange C s H D
    let R := typedRaw5 root other W Va
    let L := packedLeastProgram C X W s
    Nonempty (Derivation B Γ (unary Tg (suc z) dom ⊓ unary Tg (suc z) cod)) →
    Nonempty (Derivation B Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation B Γ (addressReport x ctx (rawCons dom cod) f)) →
    Nonempty (Derivation B Γ (addressReport y ctx (rawCons dom cod) n)) →
    Nonempty (Derivation B Γ (programGraph (rankPartitionedAddress cv tv H R L) (suc z) ![x,cert,y])) →
    Nonempty (Derivation B Γ (unary (addressScalar cv tv W L) (suc z) y)) →
    Nonempty (Derivation B Γ (leastGraph C X W s ctx cod (auxiliaryTerm dom cod f arg) value)) →
    Nonempty (Derivation B Γ (pushed C X W s R ctx cod (auxiliaryTerm dom cod n arg) value)) := by
  intro Tg Va M C W H D X R L types argument left right held scalar prior
  have got := exact_OpenRankPartitionOrdinaryFold cv tv H R L
    x cert y ctx (rawCons dom cod) f n left right held
  have form := exact_OpenOriginalSelectedGuardFormation s intrinsic T V TV baseM ctx dom cod arg types argument
  obtain ⟨scope⟩ := exact_OpenOriginalScalarAddressWindow cv tv W L y ctx (rawCons dom cod) n right scalar
  exact exact_OpenOriginalRankMeasuredForwardPath s base Va baseM g chosenCombine
    selectedGrammarOption (selectedBase intrinsic Tg) root other B α Γ ctx dom cod arg f n cert value
    form ⟨Derivation.conjunctionLeft scope⟩ got prior

#print axioms exact_OpenOriginalAllRankSelectedGuardAddressForward

theorem exact_OpenOriginalAllRankSelectedGuardAddressMatching
    (s : Settings) (base intrinsic : Program 2) (V TV T baseM cv tv g : Program 1) (root other : Program 3)
    (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (x y ctx dom cod arg f n cert value : OTerm α) :
    let Tg := conjunction (refitGuard s T) TV
    let Va := auxSyntax V TV
    let M := selectedMeasure (measureUpdate baseM chosenCombine)
    let C := factoredCover Va M selectedGrammarOption
    let W := selectedWindow s intrinsic Tg V TV baseM
    let H := auxRank g
    let D := measuredExchange M (selected (step base Va))
    let X := rankedExchange C s H D
    let R := typedRaw5 root other W Va
    let L := packedLeastProgram C X W s
    Nonempty (Derivation B Γ (unary Tg (suc z) dom ⊓ unary Tg (suc z) cod)) →
    Nonempty (Derivation B Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation B Γ (addressReport x ctx (rawCons dom cod) f)) →
    Nonempty (Derivation B Γ (addressReport y ctx (rawCons dom cod) n)) →
    Nonempty (Derivation B Γ (programGraph (rankPartitionedAddress cv tv H R L) (suc z) ![x,cert,y])) →
    Nonempty (Derivation B Γ (leastGraph C X W s ctx cod (auxiliaryTerm dom cod n arg) value)) →
    Nonempty (Derivation B Γ (pulled C X W s R ctx cod (auxiliaryTerm dom cod f arg) value)) := by
  intro Tg Va M C W H D X R L types argument left right held later
  have got := exact_OpenRankPartitionOrdinaryFold cv tv H R L
    x cert y ctx (rawCons dom cod) f n left right held
  have form := exact_OpenOriginalSelectedGuardFormation s intrinsic T V TV baseM ctx dom cod arg types argument
  obtain ⟨form⟩ := form
  obtain ⟨got⟩ := got
  obtain ⟨later⟩ := later
  obtain ⟨rule⟩ := exact_OriginalRankMeasuredMatchedPath s base Va baseM g chosenCombine
    selectedGrammarOption (selectedBase intrinsic Tg) root other B α Γ ctx dom cod arg f n cert value
  exact ⟨Derivation.implicationElimination rule
    (Derivation.conjunctionIntroduction form (Derivation.conjunctionIntroduction got later))⟩

#print axioms exact_OpenOriginalAllRankSelectedGuardAddressMatching
end LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredSelectedGuardAllRankAddressProof
