module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMeasureChildrenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMeasureChildCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMemoRowCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedRecursionOpenCutProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenThinSlotProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchMemoThinSuccessorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedAuxMeasureProof
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
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey unaryAfter binaryAfter)
open NumberedWindowInternalAuxMeasureOpenDataProof (projection nodeReports bothChildBounds)
open NumberedWindowInternalAuxMeasureOpenThinSlotProof (slotReports)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate certain shapeCheck earlierAt measureAt)
open NumberedWindowInternalScratchMemoThinSuccessorProof (exact_OpenSelectedMemoSuccessor)
open NumberedWindowInternalCoverLambdaMeasureRowTargets (lambdaMeasureUpdate)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxTape)
open NumberedWindowInternalChosenAuxMeasureMemoTargets (memoPrior)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (priorRename)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalChosenAuxMeasureCombineOpenProof (exact_OpenChosenAuxMeasureCombine)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalCoverSharedRecursionTargets
open NumberedWindowInternalCoverSharedRecursionOpenCutProof (exact_OpenCoverSharedAuxCut)
open NumberedWindowInternalCoverSharedMemoRowCasesProof (exact_OpenCoverSharedMemoRowCases)
open NumberedWindowInternalCoverSharedMeasureChildCasesProof
  (exact_OpenCoverMemoMeasuredChildCases moveMeasuredChild)
open NumberedWindowInternalCoverSharedMeasureChildrenTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenCoverSharedAuxMeasureAtRow : ExactOpenCoverSharedAuxMeasureAtRow := by
  intro M body α Γ dom cod fn arg old p mf ma df da bf ba row fnData argData
  let R := sharedMeasureUpdate M
  let prior := memoPrior dom cod fn arg
  let xs := auxTape dom cod fn arg old
  have fields := nodeReports (body := body) (Γ := Γ) dom cod fn arg old
  have small := bothChildBounds (body := body) (Γ := Γ) dom cod fn arg
  have fRow := (projection R mf fn).mp fnData.selected
  have aRow := (projection R ma arg).mp argData.selected
  have fRead := slotReports R 2 fn mf prior old fields.key fields.fnField small.1 fRow row.table
  have aRead := slotReports R 3 arg ma prior old fields.key fields.argField small.2 aRow row.table
  have guard : Nonempty (Derivation body Γ (programGraph certain (suc z) xs)) :=
    conjunctionAccept shapeCheck _ xs fields.shape
      (conjunctionAccept (earlierAt 2) (earlierAt 3) xs fRead.1 aRead.1)
  have picked := (exact_OpenCoverSharedAuxCut (measureUpdate M chosenCombine) (lambdaMeasureUpdate M)
    body α Γ dom cod fn arg old p).mp row.update
  have branch := successorBranchElim certain (unaryAfter M currentKey)
    (binaryAfter chosenCombine (measureAt 2) (measureAt 3)) p z xs guard picked
  have combined : Nonempty (Derivation body Γ (programGraph chosenCombine p ![mf,ma])) := by
    apply compositionRecover chosenCombine ![measureAt 2,measureAt 3] p xs ![mf,ma] branch
    intro i
    exact Fin.cases fRead.2 (Fin.cases aRead.2 (fun j => Fin.elim0 j)) i
  have parentRow := exact_OpenSelectedMemoSuccessor R body α Γ p prior old row.table row.update
  have selected := (projection R p (suc prior)).mpr parentRow
  have bounds := exact_OpenChosenAuxMeasureCombine body α Γ p mf ma df da bf ba
    fnData.coordinates argData.coordinates combined
  exact ⟨row,selected,fnData,argData,fRead.2,aRead.2,combined,bounds⟩

private theorem withChildren (M : Program 1) (dom cod fn arg p mf ma df da bf ba : OTerm α) (goal : Formula α)
    (parent : Nonempty (Derivation body Γ (unary (sharedMeasure M) p (auxiliaryTerm dom cod fn arg))))
    (fnData : SelectedMeasureData (sharedMeasureUpdate M) body Γ fn mf df bf)
    (argData : SelectedMeasureData (sharedMeasureUpdate M) body Γ arg ma da ba)
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (old : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      SharedAuxMeasureRow M body Δ (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)
        old (p.relabel j) (mf.relabel j) (ma.relabel j) (df.relabel j) (da.relabel j) (bf.relabel j) (ba.relabel j) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  apply exact_OpenCoverSharedMemoRowCases (sharedMeasureUpdate M) body α Γ
    (memoPrior dom cod fn arg) p goal parent
  intro β j Δ old keep row
  rw [priorRename] at row
  have f := moveMeasuredChild (sharedMeasureUpdate M) j Δ keep fnData
  have a := moveMeasuredChild (sharedMeasureUpdate M) j Δ keep argData
  exact next β j Δ old keep (exact_OpenCoverSharedAuxMeasureAtRow M body β Δ
    (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j) old (p.relabel j)
    (mf.relabel j) (ma.relabel j) (df.relabel j) (da.relabel j) (bf.relabel j) (ba.relabel j) row f a)

private theorem withFunction (M : Program 1) (dom cod fn arg p mf df bf : OTerm α) (goal : Formula α)
    (parent : Nonempty (Derivation body Γ (unary (sharedMeasure M) p (auxiliaryTerm dom cod fn arg))))
    (fnData : SelectedMeasureData (sharedMeasureUpdate M) body Γ fn mf df bf)
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (old ma da ba : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      SharedAuxMeasureRow M body Δ (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)
        old (p.relabel j) (mf.relabel j) ma (df.relabel j) da (bf.relabel j) ba →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  apply exact_OpenCoverMemoMeasuredChildCases (sharedMeasureUpdate M) body α Γ arg goal
  intro β j Δ ma da ba keep a
  have f := moveMeasuredChild (sharedMeasureUpdate M) j Δ keep fnData
  have parent' := renameInto parent j Δ keep
  rw [unaryRename,auxiliaryRename] at parent'
  apply withChildren M (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)
    (p.relabel j) (mf.relabel j) ma (df.relabel j) da (bf.relabel j) ba (goal.relabel j) parent' f a
  intro γ k Ξ old retain row
  have both (g : Formula α) (hg : g ∈ Γ) : g.relabel (k ∘ j) ∈ Ξ := by
    rw [← formulaRelabelComposition j k g]
    exact retain (g.relabel j) (keep g hg)
  simp only [Term.relabel_relabel] at row
  rw [formulaRelabelComposition j k goal]
  exact next γ (k ∘ j) Ξ old (ma.relabel k) (da.relabel k) (ba.relabel k) both row

theorem exact_OpenCoverSharedAuxMeasureParent : ExactOpenCoverSharedAuxMeasureParent := by
  intro M body α Γ dom cod fn arg p goal parent next
  apply exact_OpenCoverMemoMeasuredChildCases (sharedMeasureUpdate M) body α Γ fn goal
  intro β j Δ mf df bf keep f
  have parent' := renameInto parent j Δ keep
  rw [unaryRename,auxiliaryRename] at parent'
  apply withFunction M (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)
    (p.relabel j) mf df bf (goal.relabel j) parent' f
  intro γ k Ξ old ma da ba retain row
  have both (g : Formula α) (hg : g ∈ Γ) : g.relabel (k ∘ j) ∈ Ξ := by
    rw [← formulaRelabelComposition j k g]
    exact retain (g.relabel j) (keep g hg)
  simp only [Term.relabel_relabel] at row
  rw [formulaRelabelComposition j k goal]
  exact next γ (k ∘ j) Ξ old (mf.relabel k) ma (df.relabel k) da (bf.relabel k) ba both row

#print axioms exact_OpenCoverSharedAuxMeasureAtRow
#print axioms exact_OpenCoverSharedAuxMeasureParent

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedAuxMeasureProof
