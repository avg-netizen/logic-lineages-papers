module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginInsertionAllocationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalRawRepackThreeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanRoutedHeadProof
import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginInsertionRepackProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseParsedFoldSyntaxProof (positiveGraph)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameParser keepThrough)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept)
open NumberedWindowInternalOpenOriginScanRoutedHeadProof (loopRename)
open NumberedWindowInternalProjectedCountInductionTargets (project)
open NumberedWindowInternalProjectedCountInductionSyntaxProof (projectRename)
open NumberedWindowInternalOriginScanInductionTargets (Pools)
open NumberedWindowInternalOriginInsertionAllocationTargets (Allocated)
open NumberedWindowInternalOriginInsertionAllocationProof (exact_OpenOriginInsertionAllocation)
open NumberedWindowInternalRawRepackThreeProof (exact_OriginalRawRepackThree)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalDirectTypedUnionScratchTargets (observer)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Generate the original raw codes for both removed components, keeping
the exact physical allocation. Split the original inserted rows using the
same old and new pools, then provide both actual projections and the
exact multiplicity conservation of their ordered append. -/
theorem exact_OriginalInsertionWithRemovedRepack (r : Program 3)
    (rows removed d dl dr joined full : OTerm α) (goal : Formula α)
    (old : Nonempty (Derivation B Γ (unary parser (suc d) removed)))
    (app : Nonempty (Derivation B Γ (appendGraph joined dl dr)))
    (count : Nonempty (Derivation B Γ (observer permutation d joined)))
    (seen : Nonempty (Derivation B Γ (loopAccept r rows removed)))
    (prj : Nonempty (Derivation B Γ (project full rows)))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (rawL rawR outL outR pL pR projectedJoin : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Allocated r B Δ (rows.relabel j) (removed.relabel j) (d.relabel j) rawL rawR
        (dl.relabel j) (dr.relabel j) (joined.relabel j) (full.relabel j)
        outL outR pL pR projectedJoin →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  apply exact_OriginalRawRepackThree dl dr z goal
  intro β j Δ rawL rawR _ keep pL pR _
  have head := renameParser removed d old j Δ keep
  have both := renamePair append joined dl dr app j keep
  have cmp : Nonempty (Derivation B Δ (observer permutation (d.relabel j) (joined.relabel j))) := by
    simpa only [observer,sucRelabel,zRelabel] using renamePair permutation (suc z) d joined count j keep
  have li : Nonempty (Derivation B Δ (unary parser (suc (dl.relabel j)) rawL)) := by
    simpa only [positiveGraph,unary] using pL
  have ri : Nonempty (Derivation B Δ (unary parser (suc (dr.relabel j)) rawR)) := by
    simpa only [positiveGraph,unary] using pR
  have pools : Pools B Δ (removed.relabel j) (d.relabel j) rawL rawR
      (dl.relabel j) (dr.relabel j) (joined.relabel j) := ⟨head,li,ri,cmp,both⟩
  have sx := renameInto seen j Δ keep
  rw [loopRename] at sx
  have pj := renameInto prj j Δ keep
  rw [projectRename] at pj
  apply exact_OpenOriginInsertionAllocation r B β Δ (rows.relabel j) (removed.relabel j) (d.relabel j)
    rawL rawR (dl.relabel j) (dr.relabel j) (joined.relabel j) (full.relabel j) (goal.relabel j)
    pools sx pj
  intro γ k Ω outL outR proL proR jp carry got
  rw [formulaRelabelComposition j k goal]
  have stay := keepThrough j k keep carry
  apply next γ (k ∘ j) Ω (rawL.relabel k) (rawR.relabel k) outL outR proL proR jp stay
  simpa only [← Term.relabel_relabel] using got

#print axioms exact_OriginalInsertionWithRemovedRepack
end LogicLineages.PersistentMarking.NumberedWindowInternalOriginInsertionRepackProof
