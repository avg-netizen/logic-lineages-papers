module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityFormulaProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityPrependProof
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
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparseFieldInductionTargets (consGraph)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof (moveQuad)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt headData)
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof (positiveRename)
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishProof (fromPositive)
open NumberedWindowInternalSparsePositiveHeadDecompositionWitnessProof (provideHead)
open NumberedWindowInternalSparsePositiveHeadDecompositionChecks (exact_OpenPositiveHeadDecomposition)
open NumberedWindowInternalSparsePositiveTransitivityTargets (supplied)
open NumberedWindowInternalSparsePositiveTransitivityFormulaProof (provide suppliedRename suppliedCases)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem atNewCell (raw : Program 5) (least : Program 3)
    (ctx ty source target head next tail output : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph output head tail)))
    (advanced : Nonempty (Derivation body Γ (selectedGraph raw least (suc next) ctx ty (suc source) head)))
    (rest : Nonempty (Derivation body Γ (positiveAt raw least ctx ty next tail target))) :
    Nonempty (Derivation body Γ (supplied raw least ctx ty source target)) := by
  obtain ⟨c⟩ := cell
  obtain ⟨a⟩ := advanced
  obtain ⟨f⟩ := fromPositive raw least ctx ty next tail target rest
  have row : Nonempty (Derivation body Γ (headData raw least ctx ty source output target head tail next)) :=
    ⟨Derivation.conjunctionIntroduction c (Derivation.conjunctionIntroduction a (Derivation.conjunctionRight f))⟩
  have has := provideHead raw least ctx ty source output target head tail next row
  obtain ⟨rule⟩ := exact_OpenPositiveHeadDecomposition body raw least α ctx ty source output target
  have pos := closedApply ⟨Derivation.conjunctionRight rule⟩ has
  exact provide raw least ctx ty source target output pos

private theorem chooseNewCell (raw : Program 5) (least : Program 3)
    (ctx ty source target head next tail : OTerm α)
    (advanced : Nonempty (Derivation body Γ (selectedGraph raw least (suc next) ctx ty (suc source) head)))
    (rest : Nonempty (Derivation body Γ (positiveAt raw least ctx ty next tail target))) :
    Nonempty (Derivation body Γ (supplied raw least ctx ty source target)) := by
  apply programCases fieldCons (![head,tail] : Fin 2 → OTerm α) (supplied raw least ctx ty source target)
  intro β j Δ output hJ cell
  rw [suppliedRename]
  rw [binaryInputsRename] at cell
  have a := moveQuad j Δ hJ (advance raw least) (suc next) ctx ty (suc source) head advanced
  simp only [sucRelabel] at a
  have p := renameInto rest j Δ hJ
  rw [positiveRename] at p
  exact atNewCell raw least (ctx.relabel j) (ty.relabel j) (source.relabel j) (target.relabel j)
    (head.relabel j) (next.relabel j) (tail.relabel j) output cell a p

theorem prepend (raw : Program 5) (least : Program 3) (ctx ty source target head next : OTerm α)
    (advanced : Nonempty (Derivation body Γ (selectedGraph raw least (suc next) ctx ty (suc source) head)))
    (rest : Nonempty (Derivation body Γ (supplied raw least ctx ty next target))) :
    Nonempty (Derivation body Γ (supplied raw least ctx ty source target)) := by
  apply suppliedCases raw least ctx ty next target (supplied raw least ctx ty source target) rest
  intro β j Δ tail hJ known
  rw [suppliedRename]
  have a := moveQuad j Δ hJ (advance raw least) (suc next) ctx ty (suc source) head advanced
  simp only [sucRelabel] at a
  exact chooseNewCell raw least (ctx.relabel j) (ty.relabel j) (source.relabel j) (target.relabel j)
    (head.relabel j) (next.relabel j) tail a known

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityPrependProof
