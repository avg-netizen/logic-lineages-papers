module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionRejectGapProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionNextCodeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionForwardProof
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
open NumberedWindowInternalSparseFieldExistentialProof (consGraphRename someConsCases)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof (coords coordsRename)
open NumberedWindowInternalSparsePositiveChosenConsTargets (genuineHead)
open NumberedWindowInternalSparsePositiveChosenConsChecks (exact_OpenFinishCons)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets
open NumberedWindowInternalSparsePositiveHeadDecompositionHeadSyntaxProof (acceptedHeadRename)
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof (finishAtRename)
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishProof (fromPositive)
open NumberedWindowInternalSparsePositiveHeadDecompositionRejectGapProof (properCell)
open NumberedWindowInternalSparsePositiveHeadDecompositionNextCodeProof (selectSuccessful)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem successfulTail (raw : Program 5) (least : Program 3)
    (ctx ty source cert target hd tl next : OTerm α)
    (whole : Nonempty (Derivation body Γ (finishAt raw least ctx ty source cert target)))
    (cell : Nonempty (Derivation body Γ (consGraph cert hd tl)))
    (advanced : Nonempty (Derivation body Γ (selectedGraph raw least next ctx ty (suc source) hd))) :
    Nonempty (Derivation body Γ (hasAcceptedHead raw least ctx ty source cert target)) := by
  obtain ⟨c⟩ := cell
  obtain ⟨a⟩ := advanced
  have h : Nonempty (Derivation body Γ (genuineHead raw least ctx ty (suc source) cert hd tl next)) :=
    ⟨Derivation.conjunctionIntroduction c a⟩
  obtain ⟨rule⟩ := closedApply (exact_OpenFinishCons body raw least α (suc target) ctx ty (suc source)
    cert hd tl next) h
  obtain ⟨w⟩ := whole
  have rest := Derivation.implicationElimination (Derivation.conjunctionLeft rule) w
  exact selectSuccessful raw least ctx ty source cert target hd tl next ⟨c⟩ ⟨a⟩ ⟨rest⟩

private theorem chooseAdvance (raw : Program 5) (least : Program 3)
    (ctx ty source cert target hd tl : OTerm α)
    (whole : Nonempty (Derivation body Γ (finishAt raw least ctx ty source cert target)))
    (cell : Nonempty (Derivation body Γ (consGraph cert hd tl))) :
    Nonempty (Derivation body Γ (hasAcceptedHead raw least ctx ty source cert target)) := by
  apply programCases (advance raw least) (coords ctx ty (suc source) hd) _
  intro β j Δ next hJ advanced
  rw [acceptedHeadRename]
  rw [coordsRename,sucRelabel] at advanced
  have w := renameInto whole j Δ hJ
  rw [finishAtRename] at w
  have c := renameInto cell j Δ hJ
  rw [consGraphRename] at c
  exact successfulTail raw least (ctx.relabel j) (ty.relabel j) (source.relabel j) (cert.relabel j)
    (target.relabel j) (hd.relabel j) (tl.relabel j) next w c advanced

theorem forward (raw : Program 5) (least : Program 3) (ctx ty source cert target : OTerm α)
    (accepted : Nonempty (Derivation body Γ (positiveAt raw least ctx ty source cert target))) :
    Nonempty (Derivation body Γ (hasAcceptedHead raw least ctx ty source cert target)) := by
  have good := fromPositive raw least ctx ty source cert target accepted
  have cell := properCell raw least ctx ty source cert target good
  obtain ⟨g⟩ := good
  have whole : Nonempty (Derivation body Γ (finishAt raw least ctx ty source cert target)) :=
    ⟨Derivation.conjunctionRight g⟩
  apply someConsCases cert (hasAcceptedHead raw least ctx ty source cert target) cell
  intro β j Δ hd tl hJ row
  rw [acceptedHeadRename]
  have w := renameInto whole j Δ hJ
  rw [finishAtRename] at w
  exact chooseAdvance raw least (ctx.relabel j) (ty.relabel j) (source.relabel j) (cert.relabel j)
    (target.relabel j) hd tl w row

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionForwardProof
