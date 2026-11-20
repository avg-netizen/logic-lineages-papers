module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionFinishInputProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionWitnessProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveDeadCurrentChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionNextCodeProof
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
open NumberedWindowInternalSparseFieldInductionTargets (consGraph)
open NumberedWindowInternalSparseFieldExistentialProof (consGraphRename)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof (moveQuad)
open NumberedWindowInternalSparsePositiveFold (finish)
open NumberedWindowInternalSparsePositiveOutputTargets (args4)
open NumberedWindowInternalSparsePositiveDeadCurrentChecks (exact_OpenNoCurrentFinishZero)
open NumberedWindowInternalSparsePositiveChosenConsSyntaxProof (finishGraph finishRename)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets
open NumberedWindowInternalSparsePositiveHeadDecompositionHeadSyntaxProof (acceptedHeadRename)
open NumberedWindowInternalSparsePositiveHeadDecompositionWitnessProof (provideHead)
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishInputProof (moveInput)

attribute [local irreducible] programGraph finish advance

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem noZero (raw : Program 5) (least : Program 3) (ctx ty tail target : OTerm α)
    (psi : Formula α) (success : Nonempty (Derivation body Γ (finishGraph raw least (suc target) ctx ty z tail))) :
    Nonempty (Derivation body Γ psi) := by
  obtain ⟨absorb⟩ := exact_OpenNoCurrentFinishZero body raw least α ctx ty tail
  obtain ⟨e⟩ := valueUnique (finish raw least) (suc target) z (args4 ctx ty z tail) success
    ⟨weakenClosed absorb Γ⟩
  exact ⟨Derivation.explosion (sucNeZeroApply e)⟩

private theorem actualSuccessor (raw : Program 5) (least : Program 3)
    (ctx ty source cert target head tail encoded nextClass : OTerm α)
    (eq : Nonempty (Derivation body Γ (eqn encoded (suc nextClass))))
    (cell : Nonempty (Derivation body Γ (consGraph cert head tail)))
    (advanced : Nonempty (Derivation body Γ (selectedGraph raw least encoded ctx ty (suc source) head)))
    (tailGood : Nonempty (Derivation body Γ (finishGraph raw least (suc target) ctx ty encoded tail))) :
    Nonempty (Derivation body Γ (hasAcceptedHead raw least ctx ty source cert target)) := by
  obtain ⟨a⟩ := outputTransport (advance raw least) encoded (suc nextClass)
    (args4 ctx ty (suc source) head) eq advanced
  obtain ⟨b⟩ := moveInput raw least (suc target) ctx ty encoded (suc nextClass) tail eq tailGood
  obtain ⟨c⟩ := cell
  exact provideHead raw least ctx ty source cert target head tail nextClass
    ⟨Derivation.conjunctionIntroduction c (Derivation.conjunctionIntroduction a b)⟩

theorem selectSuccessful (raw : Program 5) (least : Program 3)
    (ctx ty source cert target head tail encoded : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph cert head tail)))
    (advanced : Nonempty (Derivation body Γ (selectedGraph raw least encoded ctx ty (suc source) head)))
    (tailGood : Nonempty (Derivation body Γ (finishGraph raw least (suc target) ctx ty encoded tail))) :
    Nonempty (Derivation body Γ (hasAcceptedHead raw least ctx ty source cert target)) := by
  let psi := hasAcceptedHead raw least ctx ty source cert target
  apply zeroSuccessorCases Γ encoded psi
  · obtain ⟨d⟩ := tailGood
    let x := eqn encoded z
    have e : Nonempty (Derivation body (x :: Γ) x) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have ok := moveInput raw least (suc target) ctx ty encoded z tail e ⟨addHyp d x⟩
    exact noZero raw least ctx ty tail target psi ok
  · intro β j Δ next hJ eq
    unfold psi
    rw [acceptedHeadRename]
    have c := renameInto cell j Δ hJ
    rw [consGraphRename] at c
    have a := moveQuad j Δ hJ (advance raw least) encoded ctx ty (suc source) head advanced
    rw [sucRelabel] at a
    have t := renameInto tailGood j Δ hJ
    rw [finishRename,sucRelabel] at t
    exact actualSuccessor raw least (ctx.relabel j) (ty.relabel j) (source.relabel j) (cert.relabel j)
      (target.relabel j) (head.relabel j) (tail.relabel j) (encoded.relabel j) next eq c a t

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionNextCodeProof
