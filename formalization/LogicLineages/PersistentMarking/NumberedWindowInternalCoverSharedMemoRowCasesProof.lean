module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMemoTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchMemoThinSuccessorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMemoRowCasesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (valueUnique outputTransport programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParser (scratchTable scratchRow)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)
open NumberedWindowInternalAuxExchangeMemoOpenTableTargets (tableAt)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureOpenDataProof (projection)
open NumberedWindowInternalScratchMemoThinSuccessorProof (exact_OpenSelectedMemoSuccessor)
open NumberedWindowInternalCoverSharedMemoTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem withTable (R : Program 4) (prior old out : OTerm α) (goal : Formula α)
    (parent : Nonempty (Derivation body Γ (unary (selectedMeasure R) out (suc prior))))
    (table : Nonempty (Derivation body Γ (tableAt R old prior)))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      ObservedStep R body Δ (prior.relabel j) (old.relabel j) (out.relabel j) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  apply programCases R ![prior,old,z,z] goal
  intro β j Δ value keep update
  simp only [quadInputsRename,zRelabel] at update
  have selected := renameInto parent j Δ keep
  have phys := renameInto table j Δ keep
  simp only [unaryRename,sucRelabel] at selected
  simp only [tableAt,programRename,tripleInputsRename,zRelabel] at phys
  let p := prior.relabel j
  let o := old.relabel j
  let x := out.relabel j
  have parentRow := (projection R x (suc p)).mp selected
  have actual := exact_OpenSelectedMemoSuccessor R body β Δ value p o phys update
  have agrees := valueUnique (scratchRow (constantZero 2) R) value x ![suc p,z,z] actual parentRow
  have aligned := outputTransport R value x ![p,o,z,z] agrees update
  exact next β j Δ keep ⟨phys,aligned⟩

theorem exact_OpenCoverSharedMemoRowCases : ExactOpenCoverSharedMemoRowCases := by
  intro R body α Γ prior out goal parent next
  apply programCases (scratchTable (constantZero 2) R) ![prior,z,z] goal
  intro β j Δ old keep table
  simp only [tripleInputsRename,zRelabel] at table
  have selected := renameInto parent j Δ keep
  simp only [unaryRename,sucRelabel] at selected
  apply withTable R (prior.relabel j) old (out.relabel j) (goal.relabel j) selected table
  intro γ k Ξ retain row
  have both (f : Formula α) (hf : f ∈ Γ) : f.relabel (k ∘ j) ∈ Ξ := by
    rw [← formulaRelabelComposition j k f]
    exact retain (f.relabel j) (keep f hf)
  simp only [Term.relabel_relabel] at row
  rw [formulaRelabelComposition j k goal]
  exact next γ (k ∘ j) Ξ (old.relabel k) both row

#print axioms exact_OpenCoverSharedMemoRowCases

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMemoRowCasesProof
