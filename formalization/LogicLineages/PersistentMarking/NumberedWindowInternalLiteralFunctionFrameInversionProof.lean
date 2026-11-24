module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFunctionGuardInversionProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenEmitProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFunctionFrameInversionProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalControlGraphSupportProof (programRename valueUnique)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalBoundedDescentNormalizerStepSupportProof (conjunctionReject)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalSparseRawFunctionFrame
open NumberedWindowInternalSparseRawFunctionFrameTargets (frameValueTerm)
open NumberedWindowInternalSparseRawFunctionFrameOpenEmitProof (emit)
open NumberedWindowInternalLiteralFunctionGuardInversionProof

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Zero is the actual rejected branch of the frame program. If the
output is a successor, the original guard has output one. -/
theorem exact_OpenFunctionFrameGuard (xs : Fin 3 → OTerm α) (o : OTerm α)
    (held : D B Γ (programGraph chosenFrame (suc o) xs)) :
    D B Γ (bit frameGood xs) := by
  let g := bit frameGood xs
  obtain ⟨hp⟩ := held
  have fn : D B (g.not :: Γ) g := by
    have nr : D B (g.not :: Γ) g.not := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have zero : D B (g.not :: Γ) (programGraph frameGood z xs) := by
      unfold frameGood
      exact conjunctionReject _ _ xs nr
    have reject := zeroBranchElim frameGood (constantZero 3) emitFrame (suc o) xs
      zero ⟨addHyp hp _⟩
    obtain ⟨err⟩ := valueUnique (constantZero 3) (suc o) z xs reject (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply err)⟩
  obtain ⟨no⟩ := fn
  exact ⟨disjunctionElimination (excludedMiddle g)
    (Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self))
    (Derivation.implicationIntroduction no)⟩

/-- A positive output of the physical contextual frame program exposes
the exact two auxiliary terms, the literal witness, exact matched
annotations and argument, and the exact successor-encoded child
frame. All of this is on arbitrary open terms in the original calculus. -/
theorem exact_OpenFunctionFrameInversion (q w r o : OTerm α) (goal : Formula α)
    (held : D B Γ (programGraph chosenFrame (suc o) ![q,w,r]))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (dom cod fn arg child dom' cod' dest arg' : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Parts B Δ (q.relabel j) (w.relabel j) (r.relabel j)
        dom cod fn arg child dom' cod' dest arg' →
      D B Δ (eqn (suc (o.relabel j)) (frameValueTerm fn child dest)) →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  apply exact_OpenFunctionGuardParts q w r goal (exact_OpenFunctionFrameGuard ![q,w,r] o held)
  intro β j Δ dom cod fn arg child dom' cod' dest arg' keep parts
  let xs : Fin 3 → OTerm β := ![q.relabel j,w.relabel j,r.relabel j]
  have h := renameInto held j Δ keep
  rw [programRename,tripleInputsRename,sucRelabel] at h
  have got := successorBranchElim frameGood (constantZero 3) emitFrame
    (suc (o.relabel j)) z xs parts.ready.guard h
  have eq := valueUnique emitFrame (suc (o.relabel j)) (frameValueTerm fn child dest)
    xs got (emit xs fn child dest parts.ready)
  exact use β j Δ dom cod fn arg child dom' cod' dest arg' keep parts eq

#print axioms exact_OpenFunctionFrameGuard
#print axioms exact_OpenFunctionFrameInversion
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFunctionFrameInversionProof
