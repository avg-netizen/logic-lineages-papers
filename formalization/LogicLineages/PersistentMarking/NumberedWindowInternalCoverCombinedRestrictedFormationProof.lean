module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFormationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFormationProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalCoverCombinedRestrictedWrappedAuxProof (exact_OpenCoverCombinedWrappedAuxFormation)
open NumberedWindowInternalCoverCombinedRestrictedFormationTargets

theorem exact_OpenCoverCombinedRestrictedFormation : ExactOpenCoverCombinedRestrictedFormation := by
  intro V TV M M0 B T s body α Γ ctx dom cod arg P W syntaxBits typeBits argument
  let j : α → α ⊕ Fin 1 := Sum.inl
  let f : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let A := windowAt W (ctx.relabel j) ((rawCons dom cod).relabel j) f
  let Δ := A :: Γ.map (fun p => p.relabel j)
  have keep (p : Formula α) (hp : p ∈ Γ) : p.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have fn : Nonempty (Derivation body Δ A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  change Nonempty (Derivation body Δ (windowAt W (ctx.relabel j) ((rawCons dom cod).relabel j) f)) at fn
  rw [rawConsRename] at fn
  have syn' := renameInto syntaxBits j Δ keep
  have ty' := renameInto typeBits j Δ keep
  have arg' := renameInto argument j Δ keep
  simp only [conjunctionRename,unaryRename,sucRelabel,zRelabel] at syn' ty'
  rw [windowRename] at arg'
  obtain ⟨formed⟩ := exact_OpenCoverCombinedWrappedAuxFormation V TV M M0 B T s body _ Δ
    (ctx.relabel j) (dom.relabel j) (cod.relabel j) f (arg.relabel j) syn' ty' fn arg'
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction formed)⟩

#print axioms exact_OpenCoverCombinedRestrictedFormation
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFormationProof
