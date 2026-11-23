module
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredSelectedGuardMatchedPathProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalAddressAtKnownFoldProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveDefinitions

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredSelectedGuardAddressMatchingProof
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
open NumberedWindowInternalMeasuredUnrestrictedSelectedFormationInputsProof (selectedWindow)
open NumberedWindowInternalThinMatchedCallsTargets (pulled)
open NumberedWindowInternalAddressAtKnownFoldProof
open NumberedWindowInternalMeasuredSelectedGuardMatchedPathProof

/-- The physical address checker supplies the exact ordinary positive
certificate at its already audited typed endpoints; the actual
application matcher retains the same endpoints and chosen argument. -/
theorem exact_OpenOriginalSelectedGuardAddressMatching
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
    Nonempty (Derivation B Γ (leastGraph C X W s ctx cod (auxiliaryTerm dom cod n arg) value)) →
    Nonempty (Derivation B Γ (pulled C X W s R ctx cod (auxiliaryTerm dom cod f arg) value)) := by
  intro Tg Va M C W X R L types argument left right held later
  have got := exact_OpenAddressAtKnownFold cv tv (positive R L) x cert y ctx (rawCons dom cod) f n left right held
  exact exact_OpenOriginalSelectedGuardMatchedPath s base intrinsic V TV T baseM root other B α Γ
    ctx dom cod arg f n cert value types argument got later

#print axioms exact_OpenOriginalSelectedGuardAddressMatching
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredSelectedGuardAddressMatchingProof
