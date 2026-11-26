module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMeasureChildrenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMeasureChildCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMemoRowCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedRecursionOpenCutProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedLambdaSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSyntaxRowLiteralReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaMeasureRowBumpProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenThinSlotProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchMemoThinSuccessorProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedLambdaMeasureProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalAuxExchangeMemoStepTargets (unaryAfter)
open NumberedWindowInternalAuxMeasureOpenDataProof (projection)
open NumberedWindowInternalAuxMeasureOpenThinSlotProof (slotReports)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate earlierAt measureAt)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalScratchMemoThinSuccessorProof (exact_OpenSelectedMemoSuccessor)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverNamedLeavesOpenDataProof (namedRename)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (lambdaPrior lambdaTape lambdaGuard lambdaShape)
open NumberedWindowInternalCoverLambdaSyntaxRowLiteralReportsProof (literalReports)
open NumberedWindowInternalCoverLambdaMeasureRowTargets (lambdaMeasureUpdate lambdaBump)
open NumberedWindowInternalCoverLambdaMeasureRowBumpProof (exact_OpenCoverLambdaBumpPair)
open NumberedWindowInternalCoverSharedRecursionTargets
open NumberedWindowInternalCoverSharedRecursionOpenCutProof (exact_OpenCoverSharedLambdaCut)
open NumberedWindowInternalCoverSharedLambdaSyntaxProof (lambdaPriorRename)
open NumberedWindowInternalCoverSharedMemoRowCasesProof (exact_OpenCoverSharedMemoRowCases)
open NumberedWindowInternalCoverSharedMeasureChildCasesProof
  (exact_OpenCoverMemoMeasuredChildCases moveMeasuredChild)
open NumberedWindowInternalCoverSharedMeasureChildrenTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenCoverSharedLambdaMeasureAtRow : ExactOpenCoverSharedLambdaMeasureAtRow := by
  intro M body α Γ ty q old p mc d b row child
  let R := sharedMeasureUpdate M
  let prior := lambdaPrior ty q
  let xs := lambdaTape ty q old
  have fields := literalReports (body := body) (Γ := Γ) ty q old
  have childRow := (projection R mc q).mp child.selected
  have read := slotReports R 1 q mc prior old fields.key fields.child fields.earlier childRow row.table
  have guard := conjunctionAccept lambdaShape (earlierAt 1) xs fields.shape read.1
  have picked := (exact_OpenCoverSharedLambdaCut (measureUpdate M chosenCombine) (lambdaMeasureUpdate M)
    body α Γ ty q old p).mp row.update
  have branch := successorBranchElim lambdaGuard (unaryAfter M NumberedWindowInternalAuxExchangeMemoStepTargets.currentKey)
    (unaryAfter lambdaBump (measureAt 1)) p z xs guard picked
  have bump : Nonempty (Derivation body Γ (unary lambdaBump p mc)) := by
    apply compositionRecover lambdaBump (fun _ : Fin 1 => measureAt 1) p xs ![mc] branch
    intro i
    obtain rfl := Fin.eq_zero i
    exact read.2
  have parentRow := exact_OpenSelectedMemoSuccessor R body α Γ p prior old row.table row.update
  have selected := (projection R p (suc prior)).mpr parentRow
  exact ⟨row,selected,child,read.2,bump,exact_OpenCoverLambdaBumpPair body α Γ p mc d b child.coordinates bump⟩

private theorem withChild (M : Program 1) (ty q p mc d b : OTerm α) (goal : Formula α)
    (parent : Nonempty (Derivation body Γ (unary (sharedMeasure M) p (lambdaTerm ty q))))
    (child : SelectedMeasureData (sharedMeasureUpdate M) body Γ q mc d b)
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (old : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      SharedLambdaMeasureRow M body Δ (ty.relabel j) (q.relabel j) old (p.relabel j)
        (mc.relabel j) (d.relabel j) (b.relabel j) → Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  apply exact_OpenCoverSharedMemoRowCases (sharedMeasureUpdate M) body α Γ (lambdaPrior ty q) p goal parent
  intro β j Δ old keep row
  rw [lambdaPriorRename] at row
  have child' := moveMeasuredChild (sharedMeasureUpdate M) j Δ keep child
  exact next β j Δ old keep (exact_OpenCoverSharedLambdaMeasureAtRow M body β Δ
    (ty.relabel j) (q.relabel j) old (p.relabel j) (mc.relabel j) (d.relabel j) (b.relabel j) row child')

theorem exact_OpenCoverSharedLambdaMeasureParent : ExactOpenCoverSharedLambdaMeasureParent := by
  intro M body α Γ ty q p goal parent next
  apply exact_OpenCoverMemoMeasuredChildCases (sharedMeasureUpdate M) body α Γ q goal
  intro β j Δ mc d b keep child
  have parent' := renameInto parent j Δ keep
  simp only [unaryRename,lambdaTerm,namedRename] at parent'
  apply withChild M (ty.relabel j) (q.relabel j) (p.relabel j) mc d b (goal.relabel j) parent' child
  intro γ k Ξ old retain row
  have both (f : Formula α) (hf : f ∈ Γ) : f.relabel (k ∘ j) ∈ Ξ := by
    rw [← formulaRelabelComposition j k f]
    exact retain (f.relabel j) (keep f hf)
  simp only [Term.relabel_relabel] at row
  rw [formulaRelabelComposition j k goal]
  exact next γ (k ∘ j) Ξ old (mc.relabel k) (d.relabel k) (b.relabel k) both row

#print axioms exact_OpenCoverSharedLambdaMeasureAtRow
#print axioms exact_OpenCoverSharedLambdaMeasureParent

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedLambdaMeasureProof
