module
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredOriginalMatchedPathProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalSelectedFormationAtGuardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineDefinitions

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredSelectedGuardMatchedPathProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z rawCons)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntax)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalFactoredCoverTargets (factoredCover)
open NumberedWindowInternalCoverSelectedGrammarOptionTargets (selectedGrammarOption)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (measuredFactoredExchange)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalMeasuredUnrestrictedSelectedFormationInputsProof (selectedBase selectedWindow)
open NumberedWindowInternalOriginalSelectedFormationAtGuardProof (exact_OpenOriginalSelectedGuardFormation)
open NumberedWindowInternalMeasuredOriginalMatchedPathProof (exact_OriginalMeasuredMatchedPath)
open NumberedWindowInternalThinMatchedCallsTargets (pulled)
open NumberedWindowInternalThinMatchedPathTargets (MatchedPathAt)

/-- In the exact original numeric-compatible measured tuple with a
literal refitted type guard and selected grammar, arbitrary originally
accepted positive certificates transport through a fixed argument.
The true input type and argument-window reports are held; the parent
formation, representative routing, and earlier application result
and positive path are produced in the same arithmetic body. -/
theorem exact_OpenOriginalSelectedGuardMatchedPath
    (s : Settings) (base intrinsic : Program 2) (V TV T baseM : Program 1) (root other : Program 3)
    (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx dom cod arg f n cert value : OTerm α) :
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
    Nonempty (Derivation B Γ (positiveAt R L ctx (rawCons dom cod) f cert n)) →
    Nonempty (Derivation B Γ (leastGraph C X W s ctx cod (auxiliaryTerm dom cod n arg) value)) →
    Nonempty (Derivation B Γ (pulled C X W s R ctx cod (auxiliaryTerm dom cod f arg) value)) := by
  intro Tg Va M C W X R L types argument original later
  obtain ⟨form⟩ := exact_OpenOriginalSelectedGuardFormation s intrinsic T V TV baseM ctx dom cod arg types argument
  obtain ⟨rule⟩ := exact_OriginalMeasuredMatchedPath s base Va baseM chosenCombine
    selectedGrammarOption (selectedBase intrinsic Tg) root other B α Γ ctx dom cod arg f n cert value
  obtain ⟨p⟩ := original
  obtain ⟨a⟩ := later
  exact ⟨Derivation.implicationElimination rule
    (Derivation.conjunctionIntroduction form (Derivation.conjunctionIntroduction p a))⟩

#print axioms exact_OpenOriginalSelectedGuardMatchedPath
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredSelectedGuardMatchedPathProof
