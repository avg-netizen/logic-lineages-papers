module

public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureMemoTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenSlotProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenTableChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureMemoChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open NumberedWindowInternalAuxExchangeMemoStepTargets (unaryAfter currentKey binaryAfter)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (binaryGraph)
open NumberedWindowInternalAuxExchangeMemoOpenTableChecks (exact_OpenSelectedMemoSuccessor)
open NumberedWindowInternalAuxMeasureStepTargets
open NumberedWindowInternalAuxMeasureOpenDataProof (nodeReports bothChildBounds projection)
open NumberedWindowInternalAuxMeasureOpenSlotProof (slotReports)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalChosenAuxMeasureCombineOpenProof (exact_OpenChosenAuxMeasureCombine)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalChosenAuxMeasureMemoTargets

/-- Same predecessor table, same row, same child reads, same chosen combine
report for both parent memo installation and the paired bound report. -/
theorem exact_OpenChosenAuxMeasureMemoRow : ExactOpenChosenAuxMeasureMemoRow := by
  intro base body α Γ dom cod fn arg mf ma df da bf ba p old R key xs parent table hf ha pf pa emit
  have fields := nodeReports (body := body) (Γ := Γ) dom cod fn arg old
  have small := bothChildBounds (body := body) (Γ := Γ) dom cod fn arg
  have fRow := (projection R mf fn).mp hf
  have aRow := (projection R ma arg).mp ha
  have fSlot := slotReports R 2 fn mf key old fields.key fields.fnField small.1 fRow table
  have aSlot := slotReports R 3 arg ma key old fields.key fields.argField small.2 aRow table
  have enough : Nonempty (Derivation body Γ (programGraph certain (suc z) xs)) :=
    conjunctionAccept shapeCheck _ xs fields.shape
      (conjunctionAccept (earlierAt 2) (earlierAt 3) xs fSlot.1 aSlot.1)
  have measured := binaryGraph chosenCombine (measureAt 2) (measureAt 3) p mf ma xs
    emit fSlot.2 aSlot.2
  have written : Nonempty (Derivation body Γ (programGraph R p xs)) :=
    successorBranchIntro certain (unaryAfter base currentKey)
      (binaryAfter chosenCombine (measureAt 2) (measureAt 3)) p z xs enough measured
  have next := exact_OpenSelectedMemoSuccessor R body α Γ p key old table written
  obtain ⟨installed⟩ := (projection R p parent).mpr next
  obtain ⟨bounds⟩ := exact_OpenChosenAuxMeasureCombine body α Γ p mf ma df da bf ba pf pa emit
  obtain ⟨shape⟩ := fields.shape
  obtain ⟨fEarlier⟩ := fSlot.1
  obtain ⟨aEarlier⟩ := aSlot.1
  obtain ⟨fRead⟩ := fSlot.2
  obtain ⟨aRead⟩ := aSlot.2
  obtain ⟨written⟩ := written
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.conjunctionIntroduction shape (Derivation.conjunctionIntroduction fEarlier aEarlier))
    (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction fRead aRead)
      (Derivation.conjunctionIntroduction written (Derivation.conjunctionIntroduction installed bounds)))⟩

#print axioms exact_OpenChosenAuxMeasureMemoRow

end LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureMemoChecks
