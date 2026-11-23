module
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredOriginalForwardPathProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalSelectedFormationAtGuardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalScalarAddressWindowProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalAddressAtKnownFoldProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveDefinitions

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredSelectedGuardAddressForwardProof
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
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (measuredFactoredExchange)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalMeasuredUnrestrictedSelectedFormationInputsProof (selectedWindow selectedBase)
open NumberedWindowInternalThinMatchedForwardBindingProof (pushed)
open NumberedWindowInternalAddressAtKnownFoldProof
open NumberedWindowInternalMeasuredOriginalForwardPathProof (exact_OpenOriginalMeasuredForwardPath)
open NumberedWindowInternalOriginalSelectedFormationAtGuardProof (exact_OpenOriginalSelectedGuardFormation)
open NumberedWindowInternalOriginalScalarAddressWindowProof
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)

theorem exact_OpenOriginalSelectedGuardAddressForward
    (s : Settings) (base intrinsic : Program 2) (V TV T baseM cv tv : Program 1) (root other : Program 3)
    (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (x y ctx dom cod arg f n cert value : OTerm α) :
    let Tg := conjunction (refitGuard s T) TV
    let Va := auxSyntax V TV
    let M := selectedMeasure (measureUpdate baseM chosenCombine)
    let C := factoredCover Va M selectedGrammarOption
    let W := selectedWindow s intrinsic Tg V TV baseM
    let X := measuredFactoredExchange s base Va baseM chosenCombine selectedGrammarOption
    let R := typedRaw5 root other W Va
    let L := packedLeastProgram C X W s
    Nonempty (Derivation B Γ (unary Tg (suc z) dom ⊓ unary Tg (suc z) cod)) →
    Nonempty (Derivation B Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation B Γ (addressReport x ctx (rawCons dom cod) f)) →
    Nonempty (Derivation B Γ (addressReport y ctx (rawCons dom cod) n)) →
    Nonempty (Derivation B Γ (programGraph (addressPositive cv tv R L) (suc z) ![x,cert,y])) →
    Nonempty (Derivation B Γ (unary (addressScalar cv tv W L) (suc z) y)) →
    Nonempty (Derivation B Γ (leastGraph C X W s ctx cod (auxiliaryTerm dom cod f arg) value)) →
    Nonempty (Derivation B Γ (pushed C X W s R ctx cod (auxiliaryTerm dom cod n arg) value)) := by
  intro Tg Va M C W X R L types argument left right held scalar prior
  have got := exact_OpenAddressAtKnownFold cv tv (positive R L) x cert y ctx (rawCons dom cod) f n left right held
  have form := exact_OpenOriginalSelectedGuardFormation s intrinsic T V TV baseM ctx dom cod arg types argument
  obtain ⟨scope⟩ := exact_OpenOriginalScalarAddressWindow cv tv W L y ctx (rawCons dom cod) n right scalar
  exact exact_OpenOriginalMeasuredForwardPath s base Va baseM chosenCombine
    selectedGrammarOption (selectedBase intrinsic Tg) root other B α Γ ctx dom cod arg f n cert value
    form ⟨Derivation.conjunctionLeft scope⟩ got prior

#print axioms exact_OpenOriginalSelectedGuardAddressForward
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredSelectedGuardAddressForwardProof
