module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityPrependProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityBindingProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionFinishInputProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveDeadCurrentChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityConsSuccessProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (zeroSuccessorCases valueUnique outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof (moveQuad)
open NumberedWindowInternalSparsePositiveFold (finish)
open NumberedWindowInternalSparsePositiveOutputTargets (args4)
open NumberedWindowInternalSparsePositiveChosenConsSyntaxProof (finishGraph finishRename)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt)
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof (positiveRename)
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishInputProof (moveInput)
open NumberedWindowInternalSparsePositiveDeadCurrentChecks (exact_OpenNoCurrentFinishZero)
open NumberedWindowInternalSparsePositiveTransitivityTargets
open NumberedWindowInternalSparsePositiveTransitivityFormulaProof (suppliedRename)
open NumberedWindowInternalSparsePositiveTransitivityBindingProof (instantiateAt uniformRename)
open NumberedWindowInternalSparsePositiveTransitivityPrependProof (prepend)

attribute [local irreducible] programGraph advance finish

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem impossibleEmpty (raw : Program 5) (least : Program 3) (ctx ty mid tail : OTerm α)
    (goal : Formula α)
    (good : Nonempty (Derivation body Γ (finishGraph raw least (suc mid) ctx ty z tail))) :
    Nonempty (Derivation body Γ goal) := by
  obtain ⟨zero⟩ := exact_OpenNoCurrentFinishZero body raw least α ctx ty tail
  obtain ⟨eq⟩ := valueUnique (finish raw least) (suc mid) z (args4 ctx ty z tail) good
    ⟨weakenClosed zero Γ⟩
  exact ⟨Derivation.explosion (sucNeZeroApply eq)⟩

private theorem useSuccessor (raw : Program 5) (least : Program 3)
    (ctx ty source head tail encoded next mid second target : OTerm α)
    (eq : Nonempty (Derivation body Γ (eqn encoded (suc next))))
    (advanced : Nonempty (Derivation body Γ (selectedGraph raw least encoded ctx ty (suc source) head)))
    (first : Nonempty (Derivation body Γ (finishGraph raw least (suc mid) ctx ty encoded tail)))
    (last : Nonempty (Derivation body Γ (positiveAt raw least ctx ty mid second target)))
    (ih : Nonempty (Derivation body Γ (uniformAt raw least ctx ty tail))) :
    Nonempty (Derivation body Γ (supplied raw least ctx ty source target)) := by
  obtain ⟨a⟩ := moveInput raw least (suc mid) ctx ty encoded (suc next) tail eq first
  obtain ⟨b⟩ := last
  obtain ⟨r⟩ := instantiateAt raw least ctx ty next tail mid second target ih
  have extended : Nonempty (Derivation body Γ (supplied raw least ctx ty next target)) :=
    ⟨Derivation.implicationElimination r (Derivation.conjunctionIntroduction a b)⟩
  have selected := outputTransport (advance raw least) encoded (suc next)
    (args4 ctx ty (suc source) head) eq advanced
  exact prepend raw least ctx ty source target head next selected extended

theorem fromAdvance (raw : Program 5) (least : Program 3)
    (ctx ty source head tail encoded mid second target : OTerm α)
    (advanced : Nonempty (Derivation body Γ (selectedGraph raw least encoded ctx ty (suc source) head)))
    (first : Nonempty (Derivation body Γ (finishGraph raw least (suc mid) ctx ty encoded tail)))
    (last : Nonempty (Derivation body Γ (positiveAt raw least ctx ty mid second target)))
    (ih : Nonempty (Derivation body Γ (uniformAt raw least ctx ty tail))) :
    Nonempty (Derivation body Γ (supplied raw least ctx ty source target)) := by
  let goal := supplied raw least ctx ty source target
  apply zeroSuccessorCases Γ encoded goal
  · obtain ⟨d⟩ := first
    let nz := eqn encoded z
    have e : Nonempty (Derivation body (nz :: Γ) nz) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have good := moveInput raw least (suc mid) ctx ty encoded z tail e ⟨addHyp d nz⟩
    exact impossibleEmpty raw least ctx ty mid tail goal good
  · intro β j Δ next hJ eq
    unfold goal
    rw [suppliedRename]
    have a := moveQuad j Δ hJ (advance raw least) encoded ctx ty (suc source) head advanced
    rw [sucRelabel] at a
    have f := renameInto first j Δ hJ
    rw [finishRename,sucRelabel] at f
    have p := renameInto last j Δ hJ
    rw [positiveRename] at p
    have h := renameInto ih j Δ hJ
    rw [uniformRename] at h
    exact useSuccessor raw least (ctx.relabel j) (ty.relabel j) (source.relabel j) (head.relabel j)
      (tail.relabel j) (encoded.relabel j) next (mid.relabel j) (second.relabel j) (target.relabel j)
      eq a f p h

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityConsSuccessProof
