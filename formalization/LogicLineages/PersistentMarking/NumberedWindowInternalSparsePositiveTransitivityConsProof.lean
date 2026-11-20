module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityConsSuccessProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityConsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparseFieldInductionTargets (consGraph)
open NumberedWindowInternalSparseFieldExistentialProof (consGraphRename)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof (coords coordsRename)
open NumberedWindowInternalSparsePositiveChosenConsTargets (genuineHead)
open NumberedWindowInternalSparsePositiveChosenConsChecks (exact_OpenFinishCons)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (finishAt positiveAt)
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof (finishAtRename positiveRename)
open NumberedWindowInternalSparsePositiveTransitivityTargets
open NumberedWindowInternalSparsePositiveTransitivityFormulaProof (suppliedRename)
open NumberedWindowInternalSparsePositiveTransitivityBindingProof (uniformRename)
open NumberedWindowInternalSparsePositiveTransitivityConsSuccessProof (fromAdvance)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem afterAdvance (raw : Program 5) (least : Program 3)
    (ctx ty source first head tail next mid second target : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph first head tail)))
    (advanceResult : Nonempty (Derivation body Γ (selectedGraph raw least next ctx ty (suc source) head)))
    (known : Nonempty (Derivation body Γ (finishAt raw least ctx ty source first mid)))
    (last : Nonempty (Derivation body Γ (positiveAt raw least ctx ty mid second target)))
    (ih : Nonempty (Derivation body Γ (uniformAt raw least ctx ty tail))) :
    Nonempty (Derivation body Γ (supplied raw least ctx ty source target)) := by
  obtain ⟨c⟩ := cell
  obtain ⟨a⟩ := advanceResult
  have proof : Nonempty (Derivation body Γ (genuineHead raw least ctx ty (suc source) first head tail next)) :=
    ⟨Derivation.conjunctionIntroduction c a⟩
  obtain ⟨equiv⟩ := closedApply (exact_OpenFinishCons body raw least α (suc mid) ctx ty (suc source)
    first head tail next) proof
  obtain ⟨f⟩ := known
  have shorter := Derivation.implicationElimination (Derivation.conjunctionLeft equiv) f
  exact fromAdvance raw least ctx ty source head tail next mid second target ⟨a⟩ ⟨shorter⟩ last ih

theorem fromCons (raw : Program 5) (least : Program 3) (ctx ty source first head tail mid second target : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph first head tail)))
    (known : Nonempty (Derivation body Γ (finishAt raw least ctx ty source first mid)))
    (last : Nonempty (Derivation body Γ (positiveAt raw least ctx ty mid second target)))
    (ih : Nonempty (Derivation body Γ (uniformAt raw least ctx ty tail))) :
    Nonempty (Derivation body Γ (supplied raw least ctx ty source target)) := by
  apply programCases (advance raw least) (coords ctx ty (suc source) head) (supplied raw least ctx ty source target)
  intro β j Δ next hJ a
  rw [suppliedRename]
  rw [coordsRename,sucRelabel] at a
  have c := renameInto cell j Δ hJ
  rw [consGraphRename] at c
  have f := renameInto known j Δ hJ
  rw [finishAtRename] at f
  have p := renameInto last j Δ hJ
  rw [positiveRename] at p
  have h := renameInto ih j Δ hJ
  rw [uniformRename] at h
  exact afterAdvance raw least (ctx.relabel j) (ty.relabel j) (source.relabel j) (first.relabel j)
    (head.relabel j) (tail.relabel j) next (mid.relabel j) (second.relabel j) (target.relabel j) c a f p h

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityConsProof
