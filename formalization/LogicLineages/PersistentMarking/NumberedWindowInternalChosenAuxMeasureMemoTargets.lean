module

public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineOpenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureMemoTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (numeral existsOne)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalAuxExchangeMemoOpenTableTargets (tableAt)
open NumberedWindowInternalAuxMeasureOpenTargets (measureGraph)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate shapeCheck earlierAt measureAt)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair boundBody)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons z suc)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)

/-- The literal unshifted physical predecessor key of this tag-six node.
The genuine case in #858 uses this key and only a table at this key. -/
abbrev memoPrior {α : Type} (dom cod fn arg : OTerm α) : OTerm α :=
  pairTerm (numeral 6) (rawCons dom (rawCons cod (rawCons fn (rawCons arg z))))

abbrev acceptedEarlierRow {α : Type} (xs : Fin 4 → OTerm α) : Formula α :=
  programGraph shapeCheck (suc z) xs ⊓
    (programGraph (earlierAt 2) (suc z) xs ⊓ programGraph (earlierAt 3) (suc z) xs)

abbrev childMemoReads {α : Type} (mf ma : OTerm α) (xs : Fin 4 → OTerm α) : Formula α :=
  programGraph (measureAt 2) mf xs ⊓ programGraph (measureAt 3) ma xs

/-- Actual chosen-combine installation in the original selected memo.
The two child reports, their original standard pair reports and the
chosen combine report all use the same measure codes. The output keeps
the actual branch guards, earlier reads and update on one fixed physical
prior table, the selected parent graph, and its weak coordinate bounds. -/
def ExactOpenChosenAuxMeasureMemoRow : Prop :=
  ∀ (base : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (dom cod fn arg mf ma df da bf ba p old : OTerm α),
    let R := measureUpdate base chosenCombine
    let key := memoPrior dom cod fn arg
    let xs : Fin 4 → OTerm α := ![key,old,z,z]
    let parent := auxiliaryTerm dom cod fn arg
    Nonempty (Derivation body Γ (tableAt R old key)) →
    Nonempty (Derivation body Γ (measureGraph base chosenCombine mf fn)) →
    Nonempty (Derivation body Γ (measureGraph base chosenCombine ma arg)) →
    Nonempty (Derivation body Γ (codePair mf df bf)) →
    Nonempty (Derivation body Γ (codePair ma da ba)) →
    Nonempty (Derivation body Γ (programGraph chosenCombine p ![mf,ma])) →
    Nonempty (Derivation body Γ (acceptedEarlierRow xs ⊓
      (childMemoReads mf ma xs ⊓ (programGraph R p xs ⊓
        (measureGraph base chosenCombine p parent ⊓ existsOne (boundBody p df da bf ba))))))

end LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureMemoTargets
