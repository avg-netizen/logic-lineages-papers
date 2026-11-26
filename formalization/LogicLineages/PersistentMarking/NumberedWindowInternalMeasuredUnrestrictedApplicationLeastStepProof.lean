module
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinPairedLeastFromCoveredWindowProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedFunctionEdgeProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedApplicationLeastStepProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (measuredFactoredExchange)
open NumberedWindowInternalMeasuredExchangeThinDefinitions (measuredExchange)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (window syntaxWindow)
open NumberedWindowInternalFactoredCoverTargets (factoredCover)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalAuxExchangeMemoTargets (selected)
open NumberedWindowInternalAuxExchangeMemoStepTargets (step)
open NumberedWindowInternalThinRoundExhaustionTargets (CountLengthBound)
open NumberedWindowInternalThinUncoveredCountTargets (InternalStrictDecrease)
open NumberedWindowInternalMeasuredUnrestrictedFunctionEdgeProof
open NumberedWindowInternalThinPairedLeastFromCoveredWindowProof

/-- The actual original application least survives a genuine measured
function edge, with unchanged argument and possibly distinct raw
function representatives. The two real typed parent windows and
literal occurrence-count theorems are explicit. -/
theorem exact_OpenMeasuredUnrestrictedApplicationLeastStep (bound : CountLengthBound) (strict : InternalStrictDecrease)
    (s : Settings) (base : Program 2) (V baseM : Program 1) (P : Program 2) (G baseW : Program 3)
    (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx dom cod f g arg x : OTerm α) :
    let M := selectedMeasure (measureUpdate baseM P)
    let C := factoredCover V M G
    let W := window C s baseW V
    let X := measuredFactoredExchange s base V baseM P G
    let a := auxiliaryTerm dom cod f arg
    let b := auxiliaryTerm dom cod g arg
    Nonempty (Derivation B Γ (acceptEdge (edge4 X W) ctx (rawCons dom cod) f g)) →
    Nonempty (Derivation B Γ (windowAt W ctx cod a)) →
    Nonempty (Derivation B Γ (windowAt W ctx cod b)) →
    Nonempty (Derivation B Γ (leastGraph C X W s ctx cod a x)) →
    Nonempty (Derivation B Γ (leastGraph C X W s ctx cod b x)) := by
  intro M C W X a b funEdge parentA parentB old
  obtain ⟨lift⟩ := exact_UnrestrictedMeasuredFunctionEdge s base V baseM P G baseW
    B α Γ ctx dom cod f g arg
  obtain ⟨funEdge⟩ := funEdge
  obtain ⟨parentA⟩ := parentA
  obtain ⟨parentB'⟩ := parentB
  have parent := Derivation.implicationElimination lift
    (Derivation.conjunctionIntroduction funEdge (Derivation.conjunctionIntroduction parentA parentB'))
  exact exact_OpenThinPairedLeastFromCoveredWindow bound strict C
    (measuredExchange M (selected (step base V))) (syntaxWindow baseW V) s ctx cod a b x
    old ⟨parent⟩ ⟨parentB'⟩

#print axioms exact_OpenMeasuredUnrestrictedApplicationLeastStep
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedApplicationLeastStepProof
