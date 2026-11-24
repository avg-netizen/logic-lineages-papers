module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBoundedFrameOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBoundedFallbackOpenProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof
  (headTransport projectionValue programRename valueUnique)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalBoundedDescentNormalizerStepSupportProof (conjunctionReject)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (frameValueTerm)
open NumberedWindowInternalLiteralBoundedFallback
open NumberedWindowInternalLiteralOrderedSelectorsProof (D)
open NumberedWindowInternalLiteralBoundedFrameOpenProof (exact_OpenBoundedFrameParts)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem clipSuccess (candidate parent pred : OTerm α)
    (held : D B Γ (programGraph clip (suc pred) ![candidate,parent])) :
    D B Γ (programGraph admitted (suc z) ![suc pred,parent]) := by
  let xs : Fin 2 → OTerm α := ![candidate,parent]
  let C := programGraph admitted (suc z) xs
  let G := programGraph admitted (suc z) ![suc pred,parent]
  obtain ⟨h⟩ := held
  have yes : D B (C :: Γ) G := by
    have guard : D B (C :: Γ) C := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have out := successorBranchElim admitted (constantZero 2) (.projection 0)
      (suc pred) z xs guard ⟨addHyp h _⟩
    have eq := valueUnique (.projection 0) candidate (suc pred) xs (projectionValue 0 xs) out
    exact headTransport admitted (suc z) candidate (suc pred) ![parent] eq guard
  have no : D B (C.not :: Γ) G := by
    have fail : D B (C.not :: Γ) (programGraph admitted z xs) := by
      unfold admitted
      exact conjunctionReject _ _ xs ⟨Derivation.hypothesis List.mem_cons_self⟩
    have out := zeroBranchElim admitted (constantZero 2) (.projection 0) (suc pred) xs fail
      ⟨addHyp h _⟩
    obtain ⟨eq⟩ := valueUnique (constantZero 2) (suc pred) z xs out (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply eq)⟩
  obtain ⟨a⟩ := yes
  obtain ⟨b⟩ := no
  exact ⟨disjunctionElimination (excludedMiddle C)
    (Derivation.implicationIntroduction a) (Derivation.implicationIntroduction b)⟩

/-- No assumption about the original callback is needed for this open
result. If the clipped fallback outputs a successor, the exact child's
witness in that output is smaller in the actual object arithmetic. -/
theorem exact_OpenDescendingFallbackParts (other : Program 3) (q parent r pred : OTerm α)
    (goal : Formula α)
    (held : D B Γ (programGraph (fallback other) (suc pred) ![q,parent,r]))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (u w v : OTerm β), (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (eqn (suc (pred.relabel j)) (frameValueTerm u w v)) →
      D B Δ (ltF w (parent.relabel j)) → D B Δ (goal.relabel j)) : D B Γ goal := by
  apply programCases other ![q,parent,r] goal
  intro β j Δ candidate keep raw
  rw [tripleInputsRename] at raw
  let xs : Fin 3 → OTerm β := ![q.relabel j,parent.relabel j,r.relabel j]
  let p := parent.relabel j
  let t := pred.relabel j
  have called := renameInto held j Δ keep
  rw [programRename,tripleInputsRename,sucRelabel] at called
  have result : D B Δ (programGraph clip (suc t) ![candidate,p]) := by
    apply compositionRecover clip ![other,.projection 1] (suc t) xs ![candidate,p] called
    intro i
    exact Fin.cases raw (Fin.cases (projectionValue 1 xs) (fun k => Fin.elim0 k)) i
  apply exact_OpenBoundedFrameParts t p (goal.relabel j) (clipSuccess candidate p t result)
  intro γ k Ω u w v stay eq order
  have all (f : Formula α) (hf : f ∈ Γ) : f.relabel (k ∘ j) ∈ Ω := by
    simpa only [formulaRelabelComposition] using stay _ (keep f hf)
  have out := use γ (k ∘ j) Ω u w v all
    (by simpa only [t,Term.relabel_relabel] using eq)
    (by simpa only [p,Term.relabel_relabel] using order)
  simpa only [formulaRelabelComposition] using out

#print axioms exact_OpenDescendingFallbackParts
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBoundedFallbackOpenProof
