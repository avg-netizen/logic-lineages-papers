module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedSharedSyntaxTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedLambdaSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedSharedStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMemoRowCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMemoLookupProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedRecursionOpenCutProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSyntaxRowLiteralReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedLambdaSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel)
open ID1Completion.InternalBetaDivisionSyntaxProof (mulRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalLessThan (ltTest)
open ID1Completion.InternalLessThanSupportProof (acceptOfLess)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBodyRename unaryRename)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalAuxExchangeMemoStepTargets (unaryAfter currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (binaryGraph)
open NumberedWindowInternalAuxMeasureStepTargets (childAt earlierAt measureAt)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets
open NumberedWindowInternalCoverLambdaSyntaxRowLiteralReportsProof (literalReports)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntaxUpdate)
open NumberedWindowInternalCoverSharedRecursionTargets
open NumberedWindowInternalCoverSharedRecursionOpenCutProof (exact_OpenCoverSharedLambdaCut)
open NumberedWindowInternalCoverSharedMemoRowCasesProof (exact_OpenCoverSharedMemoRowCases)
open NumberedWindowInternalCoverSharedMemoLookupProof (exact_OpenCoverSharedMemoEarlierValue)
open NumberedWindowInternalCoverSharedMemoTargets
open NumberedWindowInternalCoverRefinedSharedStepProof (exact_OpenCoverRefinedStep)
open NumberedWindowInternalCoverRefinedSharedSyntaxTargets
open NumberedWindowInternalCoverSharedLambdaSyntaxProof (lambdaPriorRename)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem sameRow (V T : Program 1) (ty q old : OTerm α)
    (row : ObservedStep (refinedUpdate V T) body Γ (lambdaPrior ty q) old (suc z)) :
    Nonempty (Derivation body Γ (refinedLambdaChildren V T ty q)) := by
  let R := refinedUpdate V T
  let p := lambdaPrior ty q
  let n := suc p
  let xs := lambdaTape ty q old
  have fields := literalReports (body := body) (Γ := Γ) ty q old
  have cut := (exact_OpenCoverRefinedStep V T body α Γ p old row).1
  have accepted := (exact_OpenCoverSharedLambdaCut (auxSyntaxUpdate V T) (lambdaSyntaxUpdate V T)
    body α Γ ty q old (suc z)).mp cut
  have earlier : Nonempty (Derivation body Γ (programGraph (earlierAt 1) (suc z) xs)) :=
    binaryGraph ltTest (childAt 1) currentKey (suc z) q n xs
      (acceptOfLess q n fields.earlier) fields.child fields.key
  have guard := conjunctionAccept lambdaShape (earlierAt 1) xs fields.shape earlier
  have branch := successorBranchElim lambdaGuard (unaryAfter V currentKey)
    (lambdaAccept T) (suc z) z xs guard accepted
  obtain ⟨branch⟩ := conjunctionRecover (lambdaTypeSlot T) (measureAt 1) xs branch
  have annotation : Nonempty (Derivation body Γ (unary T (suc z) ty)) := by
    apply compositionRecover T (fun _ : Fin 1 => childAt 0) (suc z) xs ![ty]
      ⟨Derivation.conjunctionLeft branch⟩
    intro i
    obtain rfl := Fin.eq_zero i
    exact fields.annotation
  obtain ⟨anno⟩ := annotation
  obtain ⟨valid⟩ := exact_OpenCoverSharedMemoEarlierValue R 1 body α Γ q p old (suc z)
    fields.key fields.child fields.earlier row.table ⟨Derivation.conjunctionRight branch⟩
  exact ⟨Derivation.conjunctionIntroduction anno valid⟩

theorem exact_OpenCoverRefinedLambdaSyntaxParent : ExactOpenCoverRefinedLambdaSyntaxParent := by
  intro V T body α Γ ty q parent
  apply exact_OpenCoverSharedMemoRowCases (refinedUpdate V T) body α Γ (lambdaPrior ty q) (suc z) _ parent
  intro β j Δ old keep row
  simp only [refinedLambdaChildren,conjunctionRename,unaryRename,zRelabel,sucRelabel]
  simp only [lambdaPriorRename,zRelabel,sucRelabel] at row
  exact sameRow V T (ty.relabel j) (q.relabel j) old row

#print axioms exact_OpenCoverRefinedLambdaSyntaxParent

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedLambdaSyntaxProof
