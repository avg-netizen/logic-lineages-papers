module
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaFrameOpenPartsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBoundedFallbackOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaFallbackOpenProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalAcceptanceSupportProof
  (compositionRecover programCases)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim zeroBranchElim)
open ID1Completion.InternalBoundedDescentNormalizerStepSupportProof (conjunctionReject)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue successorValue valueUnique outputTransport programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (frameValueTerm)
open NumberedWindowInternalSparseRawFunctionFrame (frameSlot)
open NumberedWindowInternalSparseRawTickShapeEmitterProof (consOfGraph)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralFunctionGuardFieldsProof (moveBit)
open NumberedWindowInternalLiteralLambdaFrameProof
open NumberedWindowInternalLiteralLambdaFrameOpenPartsProof
open NumberedWindowInternalLiteralBoundedFallback (fallback clip admitted)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenLambdaFrameEmit (q w r d a child e b : OTerm α)
    (row : LambdaParts B Γ q w r d a child e b) :
    D B Γ (programGraph emitLambdaFrame (frameValueTerm a child b) ![q,w,r]) := by
  let xs : Fin 3 → OTerm α := ![q,w,r]
  let tail := consOf (frameSlot 1 2) (constantZero 3)
  let mid := consOf (frameSlot 0 1) tail
  let all := consOf (frameSlot 1 0) mid
  have last := consOfGraph (frameSlot 1 2) (constantZero 3) b z xs row.targetSlot (constantZeroValue xs)
  have center := consOfGraph (frameSlot 0 1) tail child (rawCons b z) xs row.childSlot last
  have first := consOfGraph (frameSlot 1 0) mid a (rawCons child (rawCons b z)) xs row.sourceSlot center
  let tape := rawCons a (rawCons child (rawCons b z))
  apply compositionValue .succ (fun _ : Fin 1 => all) (suc tape) xs ![tape] (successorValue ![tape])
  intro j
  obtain rfl := Fin.eq_zero j
  exact first

private theorem splitFrame (q w r n : OTerm α)
    (held : D B Γ (programGraph chosenLambdaFrame (suc n) ![q,w,r])) :
    D B Γ (bit lambdaFrameGuard ![q,w,r] ⊓ programGraph emitLambdaFrame (suc n) ![q,w,r]) := by
  let xs : Fin 3 → OTerm α := ![q,w,r]
  let C := bit lambdaFrameGuard xs
  let K := C ⊓ programGraph emitLambdaFrame (suc n) xs
  obtain ⟨s⟩ := held
  have yes : D B (C :: Γ) K := by
    have c : D B (C :: Γ) C := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨v⟩ := successorBranchElim lambdaFrameGuard (constantZero 3) emitLambdaFrame
      (suc n) z xs c ⟨addHyp s _⟩
    exact ⟨Derivation.conjunctionIntroduction (Classical.choice c) v⟩
  have no : D B (C.not :: Γ) K := by
    have h : D B (C.not :: Γ) (programGraph lambdaFrameGuard z xs) := conjunctionReject _ _ xs
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have empty := zeroBranchElim lambdaFrameGuard (constantZero 3) emitLambdaFrame (suc n) xs h ⟨addHyp s _⟩
    obtain ⟨bad⟩ := valueUnique (constantZero 3) (suc n) z xs empty (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  exact ⟨disjunctionElimination (excludedMiddle C)
    (Derivation.implicationIntroduction (Classical.choice yes)) (Derivation.implicationIntroduction (Classical.choice no))⟩

/-- The successful, physically chosen lambda frame has exactly the
bound body's raw code on both sides and the actual witness selected
from the original single-child tag, not a manufactured child path. -/
theorem exact_OpenLambdaFallbackCall (other : Program 3) (q w r n : OTerm α) (goal : Formula α)
    (test : D B Γ (bit lambdaWitnessTest ![q,w,r]))
    (held : D B Γ (programGraph (lambdaFallback other) (suc n) ![q,w,r]))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (d a child e b : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      LambdaParts B Δ (q.relabel j) (w.relabel j) (r.relabel j) d a child e b →
      D B Δ (eqn (suc (n.relabel j)) (frameValueTerm a child b)) → D B Δ (goal.relabel j)) :
    D B Γ goal := by
  have atLambda := successorBranchElim lambdaWitnessTest (otherLambdaCases other) chosenLambdaFrame (suc n) z ![q,w,r] test held
  obtain ⟨pair⟩ := splitFrame q w r n atLambda
  have emit : D B Γ (programGraph emitLambdaFrame (suc n) ![q,w,r]) := ⟨Derivation.conjunctionRight pair⟩
  apply exact_OpenLambdaFrameParts q w r goal test ⟨Derivation.conjunctionLeft pair⟩
  intro β j Δ d a child e b keep row
  have actual := renameInto emit j Δ keep
  rw [programRename,tripleInputsRename,sucRelabel] at actual
  have expected := exact_OpenLambdaFrameEmit (q.relabel j) (w.relabel j) (r.relabel j) d a child e b row
  exact use β j Δ d a child e b keep row
    (valueUnique emitLambdaFrame (suc (n.relabel j)) (frameValueTerm a child b)
      ![q.relabel j,w.relabel j,r.relabel j] actual expected)

theorem exact_OpenClipKeepsCandidate (candidate parent n : OTerm α)
    (held : D B Γ (programGraph clip (suc n) ![candidate,parent])) :
    D B Γ (eqn candidate (suc n)) := by
  apply optionGraphCases admitted ![candidate,parent] _
  · intro β j Δ keep zero
    rw [binaryInputsRename] at zero
    have step := renameInto held j Δ keep
    simp only [programRename,binaryInputsRename,sucRelabel] at step
    have bad := zeroBranchElim admitted (constantZero 2) (.projection 0) (suc (n.relabel j)) _ zero step
    obtain ⟨bad⟩ := valueUnique (constantZero 2) (suc (n.relabel j)) z
      ![candidate.relabel j,parent.relabel j] bad (constantZeroValue _)
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  · intro β j Δ k keep yes
    rw [eqnRelabel,sucRelabel]
    rw [binaryInputsRename] at yes
    let ys : Fin 2 → OTerm β := ![candidate.relabel j,parent.relabel j]
    have step := renameInto held j Δ keep
    simp only [programRename,binaryInputsRename,sucRelabel] at step
    have value := successorBranchElim admitted (constantZero 2) (.projection 0) (suc (n.relabel j)) k ys yes step
    exact valueUnique (.projection 0) (candidate.relabel j) (suc (n.relabel j)) ys (projectionValue 0 ys) value

/-- The installed descending guard retains the exact candidate raw
frame, allowing the tag-one lambda callbacks and fuel proof to use
precisely the same code rather than an arbitrary frame of size three. -/
theorem exact_OpenClippedLambdaFallbackCall (other : Program 3) (q w r n : OTerm α)
    (held : D B Γ (programGraph (fallback (lambdaFallback other)) (suc n) ![q,w,r])) :
    D B Γ (programGraph (lambdaFallback other) (suc n) ![q,w,r]) := by
  apply programCases (lambdaFallback other) ![q,w,r] _
  intro β j Δ candidate keep raw
  rw [programRename,tripleInputsRename,sucRelabel]
  rw [tripleInputsRename] at raw
  let ys : Fin 3 → OTerm β := ![q.relabel j,w.relabel j,r.relabel j]
  have top := renameInto held j Δ keep
  simp only [programRename,tripleInputsRename,sucRelabel] at top
  have clipRun := compositionRecover clip ![lambdaFallback other,.projection 1] (suc (n.relabel j))
    ys ![candidate,w.relabel j] top (fun i => Fin.cases raw (Fin.cases (projectionValue 1 ys) (fun e => Fin.elim0 e)) i)
  exact outputTransport (lambdaFallback other) candidate (suc (n.relabel j)) ys
    (exact_OpenClipKeepsCandidate candidate (w.relabel j) (n.relabel j) clipRun) raw

#print axioms exact_OpenLambdaFrameEmit
#print axioms exact_OpenLambdaFallbackCall
#print axioms exact_OpenClipKeepsCandidate
#print axioms exact_OpenClippedLambdaFallbackCall
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaFallbackOpenProof
