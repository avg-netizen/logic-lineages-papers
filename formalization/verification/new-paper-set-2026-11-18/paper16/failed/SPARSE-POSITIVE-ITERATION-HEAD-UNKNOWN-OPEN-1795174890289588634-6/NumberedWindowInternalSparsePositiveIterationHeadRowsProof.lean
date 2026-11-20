module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationHeadCompareProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationHeadRowsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph stepGraph)
open NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof (moveSelected)
open NumberedWindowInternalSparsePositiveFold (iterateStep)
open NumberedWindowInternalSparsePositiveIterationBindingProof (scratchRename)
open NumberedWindowInternalSparsePositiveIterationHeadSyntaxProof
open NumberedWindowInternalSparsePositiveIterationHeadCompareProof (compareBase compareNext)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem baseRow (raw : Program 5) (least : Program 3) (p : Plan α) (old new : OTerm α)
    (before : Nonempty (Derivation body Γ (scratchGraph old p.originalCertificate p.originalCurrent)))
    (after : Nonempty (Derivation body Γ (scratchGraph new p.nextCertificate p.nextCurrent)))
    (step : Nonempty (Derivation body Γ
      (stepGraph raw least new z old p.context p.ty p.originalCurrent p.originalCertificate))) :
    Nonempty (Derivation body Γ (sameAt raw least z p)) := by
  unfold sameAt
  apply actualFiniteUniversalIntroduction body α 2 Γ
  let j : α → α ⊕ Fin 2 := Sum.inl
  let l : OTerm (α ⊕ Fin 2) := .var (.inr 0)
  let r : OTerm (α ⊕ Fin 2) := .var (.inr 1)
  let p' := p.map (fun t => t.relabel j)
  let a := oldLoop raw least p' l (suc z) ⊓ newLoop raw least p' r z
  let Δ := a :: Γ.map (fun q => q.relabel j)
  have hJ (q : Formula α) (hq : q ∈ Γ) : q.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have before' := renameInto before j Δ hJ
  have after' := renameInto after j Δ hJ
  have step' := moveSelected j Δ hJ (iterateStep raw least) new z old p.context p.ty
    p.originalCurrent p.originalCertificate step
  rw [scratchRename] at before' after'
  rw [zRelabel] at step'
  have ha : Derivation body Δ a := Derivation.hypothesis List.mem_cons_self
  obtain ⟨e⟩ := compareBase raw least p' l r (old.relabel j) (new.relabel j) before' after' step'
    ⟨Derivation.conjunctionLeft ha⟩ ⟨Derivation.conjunctionRight ha⟩
  simpa only [headMatrix,j,p',l,r,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction e))

theorem nextRow (raw : Program 5) (least : Program 3) (p : Plan α) (fuel : OTerm α)
    (equalAt : Nonempty (Derivation body Γ (sameAt raw least fuel p))) :
    Nonempty (Derivation body Γ (sameAt raw least (suc fuel) p)) := by
  unfold sameAt
  apply actualFiniteUniversalIntroduction body α 2 Γ
  let j : α → α ⊕ Fin 2 := Sum.inl
  let p' := p.map (fun t => t.relabel j)
  let l : OTerm (α ⊕ Fin 2) := .var (.inr 0)
  let r : OTerm (α ⊕ Fin 2) := .var (.inr 1)
  let f := fuel.relabel j
  let a := oldLoop raw least p' l (suc (suc f)) ⊓ newLoop raw least p' r (suc f)
  let Δ := a :: Γ.map (fun q => q.relabel j)
  have hJ (q : Formula α) (hq : q ∈ Γ) : q.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have moved := renameInto equalAt j Δ hJ
  rw [sameAtRename] at moved
  have ha : Derivation body Δ a := Derivation.hypothesis List.mem_cons_self
  obtain ⟨e⟩ := compareNext raw least p' f l r moved
    ⟨Derivation.conjunctionLeft ha⟩ ⟨Derivation.conjunctionRight ha⟩
  simpa only [headMatrix,j,p',f,l,r,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction e))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationHeadRowsProof
