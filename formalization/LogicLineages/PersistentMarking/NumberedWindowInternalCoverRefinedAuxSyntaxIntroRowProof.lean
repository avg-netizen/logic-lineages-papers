module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedAuxSyntaxIntroTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderAnyIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxIntroduceShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowThinTableProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedRecursionOpenCutProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedAuxSyntaxIntroRowProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (termReports)
open NumberedWindowInternalAuxExchangeMemoStepTargets (unaryAfter currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph)
open NumberedWindowInternalAuxMeasureOpenDataProof (projection bothChildBounds nodeReports)
open NumberedWindowInternalAuxMeasureStepTargets (childAt certain measureAt)
open NumberedWindowInternalAuxWindowOpenTargets (contextRow)
open NumberedWindowInternalStrictAuxWindowThinTableProof (earlierValue)
open NumberedWindowInternalChosenAuxMeasureMemoTargets (memoPrior)
open NumberedWindowInternalCoverSelectedValidityTargets (headerAny layout)
open NumberedWindowInternalCoverHeaderAnyIntroProof (actualHeaderAnyIntro)
open NumberedWindowInternalCoverAuxSyntaxTargets (typeAt auxAccept auxSyntaxUpdate auxTape)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (lambdaSyntaxUpdate)
open NumberedWindowInternalCoverSharedRecursionTargets (sharedSyntaxUpdate)
open NumberedWindowInternalCoverSharedRecursionOpenCutProof (exact_OpenCoverSharedAuxCut)
open NumberedWindowInternalCoverRefinedSharedSyntaxTargets (refinedUpdate refinedSyntax headerOnRow)
open NumberedWindowInternalCoverStrictAuxIntroduceShapeProof (actualAuxPhysicalData)
open NumberedWindowInternalCoverRefinedAuxSyntaxIntroTargets

attribute [local irreducible] programGraph

theorem exact_OpenCoverRefinedAuxSyntaxIntroRow : ExactOpenCoverRefinedAuxSyntaxIntroRow := by
  intro V TV body α Γ dom cod fn arg old child table
  let R : Program 4 := refinedUpdate V TV
  let prior := memoPrior dom cod fn arg
  let raw := auxiliaryTerm dom cod fn arg
  let xs : Fin 4 → OTerm α := auxTape dom cod fn arg old
  obtain ⟨children⟩ := child
  have types := Derivation.conjunctionLeft children
  have terms := Derivation.conjunctionRight children
  have actual := actualAuxPhysicalData (body := body) (Γ := Γ) z dom cod fn arg old
  have selectors := nodeReports (body := body) (Γ := Γ) dom cod fn arg old
  have order := bothChildBounds (body := body) (Γ := Γ) dom cod fn arg
  have domBit := unaryGraph TV (childAt 0) (suc z) dom xs ⟨Derivation.conjunctionLeft types⟩ actual.domain
  have codBit := unaryGraph TV (childAt 1) (suc z) cod xs ⟨Derivation.conjunctionRight types⟩ actual.codomain
  have fnRow : Nonempty (Derivation body Γ (contextRow R (suc z) fn z)) :=
    (projection R (suc z) fn).mp ⟨Derivation.conjunctionLeft terms⟩
  have argRow : Nonempty (Derivation body Γ (contextRow R (suc z) arg z)) :=
    (projection R (suc z) arg).mp ⟨Derivation.conjunctionRight terms⟩
  have fnBit := earlierValue R 2 fn (suc z) prior old z actual.function order.1 fnRow table
  have argBit := earlierValue R 3 arg (suc z) prior old z actual.argument order.2 argRow table
  let both := conjunction (measureAt 2) (measureAt 3)
  have reads := conjunctionAccept (measureAt 2) (measureAt 3) xs fnBit argBit
  have bothRead := conjunctionAccept (typeAt TV 1) both xs codBit reads
  have admitted := conjunctionAccept (typeAt TV 0) (conjunction (typeAt TV 1) both) xs domBit bothRead
  have auxRow : Nonempty (Derivation body Γ (programGraph (auxSyntaxUpdate V TV) (suc z) xs)) :=
    successorBranchIntro certain (unaryAfter V currentKey) (auxAccept TV)
      (suc z) z xs actual.bothEarlier admitted
  have shared := (exact_OpenCoverSharedAuxCut (auxSyntaxUpdate V TV) (lambdaSyntaxUpdate V TV)
    body α Γ dom cod fn arg old (suc z)).mpr auxRow
  obtain ⟨shape,_⟩ := termReports (body := body) (Γ := Γ) dom cod fn arg
  have header := actualHeaderAnyIntro layout 6 4 raw (by simp [layout]) shape
  have headerOnActualRow := unaryGraph (headerAny layout) currentKey (suc z) raw xs header selectors.key
  exact conjunctionAccept (sharedSyntaxUpdate V TV) headerOnRow xs shared headerOnActualRow

#print axioms exact_OpenCoverRefinedAuxSyntaxIntroRow

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedAuxSyntaxIntroRowProof
