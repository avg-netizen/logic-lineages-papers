module

public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureMemoTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalAuxMeasureOpenTargets (measureGraph)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair boundBody)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)

abbrev parentMeasureAndBounds {α : Type} (base : Program 1)
    (dom cod fn arg p df da bf ba : OTerm α) : Formula α :=
  measureGraph base chosenCombine p (auxiliaryTerm dom cod fn arg) ⊓
    existsOne (boundBody p df da bf ba)

/-- The actual selected parent value and its paired weak bounds from
genuine child reports and the chosen combine. No prior table premise:
the proof observes the physical table at the literal parent predecessor. -/
def ExactOpenChosenAuxMeasureObserved : Prop :=
  ∀ (base : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (dom cod fn arg mf ma df da bf ba p : OTerm α),
    Nonempty (Derivation body Γ (measureGraph base chosenCombine mf fn)) →
    Nonempty (Derivation body Γ (measureGraph base chosenCombine ma arg)) →
    Nonempty (Derivation body Γ (codePair mf df bf)) →
    Nonempty (Derivation body Γ (codePair ma da ba)) →
    Nonempty (Derivation body Γ (programGraph chosenCombine p ![mf,ma])) →
    Nonempty (Derivation body Γ (parentMeasureAndBounds base dom cod fn arg p df da bf ba))

end LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedTargets
