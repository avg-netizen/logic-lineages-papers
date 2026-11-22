module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMemoTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMemoRowCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMemoLookupProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedRecursionOpenCutProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenThinSlotProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedAuxSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (valueUnique outputTransport programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptance (constantZero conjunction)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.InternalLessThan (ltTest)
open ID1Completion.InternalLessThanSupportProof (acceptOfLess)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (termReports)
open NumberedWindowInternalSparseFieldParser (scratchRow)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)
open NumberedWindowInternalAuxExchangeMemoStepTargets (unaryAfter currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph binaryGraph)
open NumberedWindowInternalAuxMeasureStepTargets (certain shapeCheck childAt earlierAt measureAt)
open NumberedWindowInternalAuxExchangeMemoOpenTableTargets (readRow tableAt)
open NumberedWindowInternalAuxMeasureOpenThinSlotProof (slotReports)
open NumberedWindowInternalAuxMeasureOpenDataProof (nodeReports bothChildBounds projection)
open NumberedWindowInternalChosenAuxMeasureMemoTargets (memoPrior)
open NumberedWindowInternalCoverAuxSyntaxTargets
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (lambdaSyntaxUpdate)
open NumberedWindowInternalCoverSharedRecursionTargets
open NumberedWindowInternalCoverSharedRecursionOpenCutProof (exact_OpenCoverSharedAuxCut)
open NumberedWindowInternalCoverSharedMemoRowCasesProof (exact_OpenCoverSharedMemoRowCases)
open NumberedWindowInternalCoverSharedMemoLookupProof (exact_OpenCoverSharedMemoEarlierValue)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (priorRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open NumberedWindowInternalCoverSharedMemoTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem typeReport (T : Program 1) (slot : Nat) (ty : OTerm α) (xs : Fin 4 → OTerm α)
    (selected : Nonempty (Derivation body Γ (programGraph (childAt slot) ty xs)))
    (accepted : Nonempty (Derivation body Γ (programGraph (typeAt T slot) (suc z) xs))) :
    Nonempty (Derivation body Γ (unary T (suc z) ty)) := by
  apply compositionRecover T (fun _ : Fin 1 => childAt slot) (suc z) xs ![ty] accepted
  intro i
  obtain rfl := Fin.eq_zero i
  exact selected

private theorem sameRow (V T : Program 1) (dom cod fn arg old : OTerm α)
    (row : ObservedStep (sharedSyntaxUpdate V T) body Γ (memoPrior dom cod fn arg) old (suc z)) :
    Nonempty (Derivation body Γ (sharedAuxChildren V T dom cod fn arg)) := by
  let R := sharedSyntaxUpdate V T
  let prior := memoPrior dom cod fn arg
  let parent := auxiliaryTerm dom cod fn arg
  let xs := auxTape dom cod fn arg old
  have fields := nodeReports (body := body) (Γ := Γ) dom cod fn arg old
  have small := bothChildBounds (body := body) (Γ := Γ) dom cod fn arg
  have fEarlier : Nonempty (Derivation body Γ (programGraph (earlierAt 2) (suc z) xs)) :=
    binaryGraph ltTest (childAt 2) currentKey (suc z) fn parent xs
      (acceptOfLess fn parent small.1) fields.fnField fields.key
  have aEarlier : Nonempty (Derivation body Γ (programGraph (earlierAt 3) (suc z) xs)) :=
    binaryGraph ltTest (childAt 3) currentKey (suc z) arg parent xs
      (acceptOfLess arg parent small.2) fields.argField fields.key
  have guard : Nonempty (Derivation body Γ (programGraph certain (suc z) xs)) :=
    conjunctionAccept shapeCheck _ xs fields.shape
      (conjunctionAccept (earlierAt 2) (earlierAt 3) xs fEarlier aEarlier)
  have accepted := (exact_OpenCoverSharedAuxCut (auxSyntaxUpdate V T) (lambdaSyntaxUpdate V T)
    body α Γ dom cod fn arg old (suc z)).mp row.update
  have branch := successorBranchElim certain (unaryAfter V currentKey) (auxAccept T) (suc z) z xs guard accepted
  obtain ⟨d⟩ := conjunctionRecover (typeAt T 0)
    (conjunction (typeAt T 1) (conjunction (measureAt 2) (measureAt 3))) xs branch
  obtain ⟨c⟩ := conjunctionRecover (typeAt T 1) (conjunction (measureAt 2) (measureAt 3)) xs
    ⟨Derivation.conjunctionRight d⟩
  obtain ⟨bits⟩ := conjunctionRecover (measureAt 2) (measureAt 3) xs ⟨Derivation.conjunctionRight c⟩
  obtain ⟨_,rawFields⟩ := termReports (body := body) (Γ := Γ) dom cod fn arg
  have domSlot := unaryGraph (field 0) currentKey dom parent xs rawFields.1 fields.key
  have codSlot := unaryGraph (field 1) currentKey cod parent xs rawFields.2.1 fields.key
  obtain ⟨domBit⟩ := typeReport T 0 dom xs domSlot ⟨Derivation.conjunctionLeft d⟩
  obtain ⟨codBit⟩ := typeReport T 1 cod xs codSlot ⟨Derivation.conjunctionLeft c⟩
  obtain ⟨fnBit⟩ := exact_OpenCoverSharedMemoEarlierValue R 2 body α Γ fn prior old (suc z)
    fields.key fields.fnField small.1 row.table
    ⟨Derivation.conjunctionLeft bits⟩
  obtain ⟨argBit⟩ := exact_OpenCoverSharedMemoEarlierValue R 3 body α Γ arg prior old (suc z)
    fields.key fields.argField small.2 row.table
    ⟨Derivation.conjunctionRight bits⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction domBit codBit)
    (Derivation.conjunctionIntroduction fnBit argBit)⟩

theorem exact_OpenCoverSharedAuxSyntaxParent : ExactOpenCoverSharedAuxSyntaxParent := by
  intro V T body α Γ dom cod fn arg parent
  apply exact_OpenCoverSharedMemoRowCases (sharedSyntaxUpdate V T) body α Γ
    (memoPrior dom cod fn arg) (suc z) _ parent
  intro β j Δ old keep row
  simp only [sharedAuxChildren,conjunctionRename,unaryRename,zRelabel,sucRelabel]
  simp only [priorRename,zRelabel,sucRelabel] at row
  exact sameRow V T (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j) old row

#print axioms exact_OpenCoverSharedAuxSyntaxParent

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedAuxSyntaxProof
