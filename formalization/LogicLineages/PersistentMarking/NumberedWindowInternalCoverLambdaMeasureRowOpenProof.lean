module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaMeasureRowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaMeasureRowBumpProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSyntaxRowLiteralReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenThinSlotProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchMemoThinSuccessorProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaMeasureRowOpenProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalAuxExchangeMemoStepTargets (unaryAfter currentKey)
open NumberedWindowInternalAuxMeasureStepTargets (earlierAt measureAt)
open NumberedWindowInternalAuxMeasureOpenThinSlotProof (slotReports)
open NumberedWindowInternalAuxMeasureOpenDataProof (projection)
open NumberedWindowInternalScratchMemoThinSuccessorProof (exact_OpenSelectedMemoSuccessor)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets
open NumberedWindowInternalCoverLambdaSyntaxRowLiteralReportsProof (literalReports)
open NumberedWindowInternalCoverLambdaMeasureRowTargets
open NumberedWindowInternalCoverLambdaMeasureRowBumpProof (exact_OpenCoverLambdaBumpPair)

attribute [local irreducible] programGraph

theorem exact_OpenCoverLambdaMeasureRow : ExactOpenCoverLambdaMeasureRow := by
  intro M body α Γ ty q old mc p d w table actual child code
  let R := lambdaMeasureUpdate M
  let prior := lambdaPrior ty q
  let xs := lambdaTape ty q old
  have fields := literalReports (body := body) (Γ := Γ) ty q old
  have childRow := (projection R mc q).mp child
  have reads := slotReports R 1 q mc prior old fields.key fields.child fields.earlier childRow table
  have guard := conjunctionAccept lambdaShape (earlierAt 1) xs fields.shape reads.1
  have row := successorBranchElim lambdaGuard (unaryAfter M currentKey)
    (unaryAfter lambdaBump (measureAt 1)) p z xs guard actual
  have bump : Nonempty (Derivation body Γ (unary lambdaBump p mc)) := by
    apply compositionRecover lambdaBump (fun _ : Fin 1 => measureAt 1) p xs ![mc] row
    intro i
    obtain rfl := Fin.eq_zero i
    exact reads.2
  obtain ⟨paired⟩ := exact_OpenCoverLambdaBumpPair body α Γ p mc d w code bump
  have installed := exact_OpenSelectedMemoSuccessor R body α Γ p prior old table actual
  obtain ⟨parent⟩ := (projection R p (lambdaTerm ty q)).mpr installed
  obtain ⟨earlier⟩ := reads.1
  obtain ⟨lookup⟩ := reads.2
  exact ⟨Derivation.conjunctionIntroduction parent
    (Derivation.conjunctionIntroduction paired (Derivation.conjunctionIntroduction earlier lookup))⟩

#print axioms exact_OpenCoverLambdaMeasureRow

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaMeasureRowOpenProof
